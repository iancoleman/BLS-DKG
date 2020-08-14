// Copyright 2020 MaidSafe.net limited.
//
// This SAFE Network Software is licensed to you under the MIT license <LICENSE-MIT
// https://opensource.org/licenses/MIT> or the Modified BSD license <LICENSE-BSD
// https://opensource.org/licenses/BSD-3-Clause>, at your option. This file may not be copied,
// modified, or distributed except according to those terms. Please review the Licences for the
// specific language governing permissions and limitations relating to use of the SAFE Network
// Software.

mod encryptor;
pub mod message;
pub mod outcome;
mod rng_adapter;

#[cfg(test)]
mod tests;

use crate::id::{PublicId, SecretId};
use bincode::{self, deserialize, serialize};
use encryptor::{Encryptor, Iv, Key};
use message::Message;
use outcome::Outcome;
use rand::{self, RngCore};
use serde_derive::{Deserialize, Serialize};
use std::collections::{btree_map::Entry, BTreeMap, BTreeSet};
use std::{
    fmt::{self, Debug, Formatter},
    mem,
};
use threshold_crypto::{
    ff::Field,
    group::CurveAffine,
    poly::{BivarCommitment, BivarPoly, Poly},
    serde_impl::FieldWrap,
    Fr, G1Affine, SecretKeyShare,
};

/// A local error while handling a message, that was not caused by that message being invalid.
#[derive(Clone, Eq, err_derive::Error, PartialEq, Debug)]
pub enum Error {
    /// Unknown error.
    #[error(display = "Unknown")]
    Unknown,
    /// Unknown sender.
    #[error(display = "Unknown sender")]
    UnknownSender,
    /// Failed to serialize message.
    #[error(display = "Serialization error: {}", _0)]
    Serialization(String),
    /// Network error from Quic-P2P.
    #[error(display = "QuicP2P error: {}", _0)]
    QuicP2P(String),
    /// Failed to encrypt message.
    #[error(display = "Encryption error")]
    Encryption,
    /// Failed to finalize Complaint phase due to too many non-voters.
    #[error(display = "Too many non-voters error")]
    TooManyNonVoters(BTreeSet<u64>),
    /// Unexpected phase.
    #[error(display = "Unexpected phase")]
    UnexpectedPhase { expected: Phase, actual: Phase },
    /// Ack on a missed part.
    #[error(display = "ACK on missed contribution")]
    MissingContribution,
}

impl From<Box<bincode::ErrorKind>> for Error {
    fn from(err: Box<bincode::ErrorKind>) -> Error {
        Error::Serialization(format!("{:?}", err))
    }
}

/// A contribution by a node for the key generation. The contribution shall only be handled by the receiver.
#[derive(Deserialize, Serialize, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Contribution {
    // Index of the peer that expected to receive this Contribution.
    consumer: u64,
    // Poly-commitment for the consumer to consume.
    consumable_commitment: BivarCommitment,
    // serialized row for the consumer.
    ser_row: Vec<u8>,
    // Encrypted rows from the creator.
    enc_rows: Vec<Vec<u8>>,
}

impl Debug for Contribution {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Part")
            .field(&format!("<consumer {}>", &self.consumer))
            .field(&format!("<degree {}>", self.consumable_commitment.degree()))
            .field(&format!("<{} rows>", self.enc_rows.len()))
            .finish()
    }
}

/// A confirmation that we have received and verified a validator's part. It must be sent to
/// all participating nodes and handled by all of them, including ourselves.
///
/// The message is only produced after we verified our row against the ack in the `Contribution`.
/// For each node, it contains `proposal_index, receiver_index, serialised value for the receiver,
/// encrypted values from the sender`.
#[derive(Deserialize, Serialize, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Acknowledgment(u64, u64, Vec<u8>, Vec<Vec<u8>>);

impl Debug for Acknowledgment {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Acknowledgment")
            .field(&format!("<proposer {}>", &self.0))
            .field(&format!("<receiver {}>", &self.1))
            .field(&format!("<{} values>", self.3.len()))
            .finish()
    }
}

/// The information needed to track a single contributor's secret sharing process.
#[derive(Debug, PartialEq, Eq)]
struct ContributionTracker {
    /// The contributors commitment.
    commitment_from_contribution: BivarCommitment,
    /// The verified values we received from `Acknowledgment` messages.
    verified_values: BTreeMap<u64, Fr>,
    /// The encrypted values received from the contributor.
    enc_values: Vec<Vec<u8>>,
    /// The nodes which have committed.
    acks: BTreeSet<u64>,
}

impl ContributionTracker {
    /// Creates a new part state with a commitment.
    fn new(commitment_from_contribution: BivarCommitment) -> ContributionTracker {
        ContributionTracker {
            commitment_from_contribution,
            verified_values: BTreeMap::new(),
            enc_values: Vec::new(),
            acks: BTreeSet::new(),
        }
    }

    fn is_complete(&self, threshold: usize) -> bool {
        self.acks.len() > threshold
    }
}

impl<'a> serde::Deserialize<'a> for ContributionTracker {
    fn deserialize<D: serde::Deserializer<'a>>(deserializer: D) -> Result<Self, D::Error> {
        let (commitment_from_contribution, verified_values, enc_values, acks) = serde::Deserialize::deserialize(deserializer)?;
        let verified_values: Vec<(u64, FieldWrap<Fr>)> = verified_values;
        Ok(Self {
            commitment_from_contribution,
            verified_values: verified_values
                .into_iter()
                .map(|(index, fr)| (index, fr.0))
                .collect(),
            enc_values,
            acks,
        })
    }
}

/// The outcome of handling and verifying a `Contribution` message.
pub enum ContributionOutcome {
    /// The message was valid: the part of it that was encrypted to us matched the public
    /// ack, so we can multicast an `Acknowledgment` message for it. If we have already handled the
    /// same `Contribution` before, this contains `None` instead.
    Valid(Option<Acknowledgment>),
    /// The message was invalid: We now know that the contributor is faulty.
    Invalid(ContributionFault),
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
pub enum Phase {
    Initialize,
    Contribute,
    Complain,
    Justify,
    Combine,
    Finalize,
}

#[derive(Default)]
struct InitializationAccumulator<P: PublicId> {
    senders: BTreeSet<u64>,
    initializations: BTreeMap<(usize, usize, BTreeSet<P>), usize>,
}

impl<P: PublicId> InitializationAccumulator<P> {
    fn new() -> InitializationAccumulator<P> {
        InitializationAccumulator {
            senders: BTreeSet::new(),
            initializations: BTreeMap::new(),
        }
    }

    fn add_initialization(
        &mut self,
        // Following the `m of n` terminology, here m is the threshold and n is the total number.
        m: usize,
        n: usize,
        sender: u64,
        member_list: BTreeSet<P>,
    ) -> Option<(usize, usize, BTreeSet<P>)> {
        if !self.senders.insert(sender) {
            return None;
        }

        let paras = (m, n, member_list);
        if let Some(value) = self.initializations.get_mut(&paras) {
            *value += 1;
            if *value >= m {
                return Some(paras);
            }
        } else {
            let _ = self.initializations.insert(paras, 1);
        }
        None
    }
}

#[derive(Default)]
struct ComplaintsAccumulator<P: PublicId> {
    pub_keys: BTreeSet<P>,
    threshold: usize,
    // Indexed by complaining targets.
    complaints: BTreeMap<P, BTreeSet<P>>,
}

impl<P: PublicId> ComplaintsAccumulator<P> {
    fn new(pub_keys: BTreeSet<P>, threshold: usize) -> ComplaintsAccumulator<P> {
        ComplaintsAccumulator {
            pub_keys,
            threshold,
            complaints: BTreeMap::new(),
        }
    }

    // TODO: accusation shall be validated.
    fn add_complaint(&mut self, sender_id: P, target_id: P, _msg: Vec<u8>) {
        if !self.pub_keys.contains(&sender_id) || !self.pub_keys.contains(&target_id) {
            return;
        }

        match self.complaints.entry(target_id.clone()) {
            Entry::Occupied(mut entry) => {
                let _ = entry.get_mut().insert(sender_id);
            }
            Entry::Vacant(entry) => {
                let mut targets = BTreeSet::new();
                let _ = targets.insert(target_id);
                let _ = entry.insert(targets);
            }
        }
    }

    // Returns the invalid peers that quorumn members complained against, together with the
    // non-contributors. Both shall be considered as invalid participants.
    fn finalize_complaining_phase(&self) -> BTreeSet<P> {
        let mut invalid_peers = BTreeSet::new();

        // Counts for how many times a member missed complaining against others validly.
        // If missed too many times, such member shall be considered as invalid directly.
        let mut counts: BTreeMap<P, usize> = BTreeMap::new();

        for (target_id, accusers) in self.complaints.iter() {
            if accusers.len() > self.pub_keys.len() - self.threshold {
                let _ = invalid_peers.insert(target_id.clone());
                for peer in self.pub_keys.iter() {
                    if !accusers.contains(peer) {
                        *counts.entry(peer.clone()).or_insert(0usize) += 1;
                    }
                }
            }
        }
        for (peer, times) in counts {
            if times > self.pub_keys.len() / 2 {
                let _ = invalid_peers.insert(peer);
            }
        }

        invalid_peers
    }
}

/// An algorithm for dealerless distributed key generation.
///
/// This is trying to follow the protocol as suggested at
/// https://github.com/dashpay/dips/blob/master/dip-0006/bls_m-of-n_threshold_scheme_and_dkg.md#distributed-key-generation-dkg-protocol
///
/// A normal usage flow will be:
///   a, call `initialize` first to generate an instance.
///   b, multicasting the return `Message` to all participants.
///   c, call `handle_message` function to handle the incoming `Message` and multicasting the
///      resulted `Message` (if has) to all participants.
///   d, call `finalize_complaining_phase` to complete the complaining phase. (This separate call may need to
///      depend on a separate timer & checker against the key generator's current status)
///   e, repeat step c when there is incoming `Message`.
///   f, call `generate_keys` to get the public-key set and secret-key share, if the procedure finalized.
pub struct KeyGen<S: SecretId> {
    /// Our node ID.
    our_id: S::PublicId,
    /// Our node index.
    our_index: u64,
    /// The public keys of all nodes, by node ID.
    pub_keys: BTreeSet<S::PublicId>,
    /// Carry out encryption work during the DKG process.
    encryptor: Encryptor<S::PublicId>,
    /// Proposed bivariate polynomials that must be tracked for validity and acknowledgement.
    contribution_trackers: BTreeMap<u64, ContributionTracker>,
    /// The degree of the generated polynomial.
    threshold: usize,
    /// Current DKG phase.
    phase: Phase,
    /// Accumulates initializations.
    initalization_accumulator: InitializationAccumulator<S::PublicId>,
    /// Accumulates complaints.
    complaints_accumulator: ComplaintsAccumulator<S::PublicId>,
    /// Pending complain messages.
    pending_complain_messages: Vec<Message<S::PublicId>>,
    /// Pending messages that cannot handle yet.
    pending_messags: Vec<Message<S::PublicId>>,
}

impl<S: SecretId> KeyGen<S> {
    /// Creates a new `KeyGen` instance, together with the `Initial` message that should be
    /// multicast to all nodes.
    pub fn initialize(
        sec_key: &S,
        threshold: usize,
        pub_keys: BTreeSet<S::PublicId>,
    ) -> Result<(KeyGen<S>, Message<S::PublicId>), Error> {
        if pub_keys.len() < threshold {
            return Err(Error::Unknown);
        }
        let our_id = sec_key.public_id().clone();
        let our_index = if let Some(index) = pub_keys.iter().position(|id| *id == our_id) {
            index as u64
        } else {
            return Err(Error::Unknown);
        };

        let key_gen = KeyGen::<S> {
            our_id,
            our_index,
            pub_keys: pub_keys.clone(),
            encryptor: Encryptor::new(&pub_keys),
            contribution_trackers: BTreeMap::new(),
            threshold,
            phase: Phase::Initialize,
            initalization_accumulator: InitializationAccumulator::new(),
            complaints_accumulator: ComplaintsAccumulator::new(pub_keys.clone(), threshold),
            pending_complain_messages: Vec::new(),
            pending_messags: Vec::new(),
        };

        Ok((
            key_gen,
            Message::Initialization {
                key_gen_id: our_index,
                m: threshold,
                n: pub_keys.len(),
                member_list: pub_keys,
            },
        ))
    }

    pub fn phase(&self) -> Phase {
        self.phase
    }

    /// Dispatching an incoming dkg message.
    pub fn handle_message<R: RngCore>(
        &mut self,
        rng: &mut R,
        msg: Message<S::PublicId>,
    ) -> Result<Vec<Message<S::PublicId>>, Error> {
        if self.is_finalized() {
            return Ok(Vec::new());
        }
        let result = self.process_message(rng, msg.clone());
        match result {
            Ok(mut msgs) => {
                msgs.extend(self.poll_pending_messages(rng));
                Ok(msgs)
            }
            Err(Error::UnexpectedPhase { .. }) | Err(Error::MissingContribution) => {
                self.pending_messags.push(msg);
                Ok(Vec::new())
            }
            Err(_) => result,
        }
    }

    fn poll_pending_messages<R: RngCore>(&mut self, rng: &mut R) -> Vec<Message<S::PublicId>> {
        let pending_messags = std::mem::replace(&mut self.pending_messags, Vec::new());
        let mut msgs = Vec::new();
        for message in pending_messags {
            if let Ok(new_messages) = self.process_message(rng, message.clone()) {
                if self.is_finalized() {
                    return Vec::new();
                }
                msgs.extend(new_messages);
            } else {
                self.pending_messags.push(message);
            }
        }
        msgs
    }

    fn process_message<R: RngCore>(
        &mut self,
        rng: &mut R,
        msg: Message<S::PublicId>,
    ) -> Result<Vec<Message<S::PublicId>>, Error> {
        debug!(
            "{:?} with phase {:?} handle DKG message {:?}",
            self, self.phase, msg
        );
        match msg {
            Message::Initialization {
                key_gen_id,
                m,
                n,
                member_list,
            } => self.handle_initialization(rng, m, n, key_gen_id, member_list),
            Message::Contribution { key_gen_id, contribution } => self.handle_contribution(key_gen_id, contribution),
            Message::Complaint {
                key_gen_id,
                target,
                msg,
            } => self.handle_complaint(key_gen_id, target, msg),
            Message::Justification {
                key_gen_id,
                keys_map,
            } => self.handle_justification(key_gen_id, keys_map),
            Message::Acknowledgment { key_gen_id, ack } => self.handle_ack(key_gen_id, ack),
        }
    }

    // Handles an incoming initialize message. Creates the `Proposal` message once quorumn
    // agreement reached, and the message should be multicast to all nodes.
    fn handle_initialization<R: RngCore>(
        &mut self,
        rng: &mut R,
        m: usize,
        n: usize,
        sender: u64,
        member_list: BTreeSet<S::PublicId>,
    ) -> Result<Vec<Message<S::PublicId>>, Error> {
        if self.phase != Phase::Initialize {
            return Err(Error::UnexpectedPhase {
                expected: Phase::Initialize,
                actual: self.phase,
            });
        }

        if let Some((m, _n, member_list)) =
            self.initalization_accumulator
                .add_initialization(m, n, sender, member_list)
        {
            self.threshold = m;
            self.pub_keys = member_list;
            self.phase = Phase::Contribute;

            let mut rng = rng_adapter::RngAdapter(&mut *rng);
            let our_contribution = BivarPoly::random(self.threshold, &mut rng);
            let our_commitment = our_contribution.commitment();
            let encrypt = |(i, pk): (usize, &S::PublicId)| {
                let row = our_contribution.row(i + 1);
                self.encryptor.encrypt(pk, &serialize(&row)?)
            };
            let rows = self
                .pub_keys
                .iter()
                .enumerate()
                .map(encrypt)
                .collect::<Result<Vec<_>, Error>>()?;
            let result = self
                .pub_keys
                .iter()
                .enumerate()
                .map(|(idx, _pk)| {
                    let ser_row = serialize(&our_contribution.row(idx + 1))?;
                    Ok(Message::Contribution {
                        key_gen_id: self.our_index,
                        contribution: Contribution {
                            consumer: idx as u64,
                            consumable_commitment: our_commitment.clone(),
                            ser_row,
                            enc_rows: rows.clone(),
                        },
                    })
                })
                .collect::<Result<Vec<_>, Error>>()?;
            return Ok(result);
        }
        Ok(Vec::new())
    }

    // Handles a `Contribution` message during the `Contribution` phase.
    // When there is an invalidation happens, holds the `Complaint` message till broadcast out
    // when `finalize_contributing` being called.
    fn handle_contribution(
        &mut self,
        sender_index: u64,
        contribution: Contribution,
    ) -> Result<Vec<Message<S::PublicId>>, Error> {
        if !(self.phase == Phase::Contribute || self.phase == Phase::Combine) {
            return Err(Error::UnexpectedPhase {
                expected: Phase::Contribute,
                actual: self.phase,
            });
        }

        let row = match self.handle_contribution_or_fault(sender_index, contribution.clone()) {
            Ok(Some(row)) => row,
            Ok(None) => return Ok(Vec::new()),
            Err(_fault) => {
                let msg = Message::Contribution::<S::PublicId> {
                    key_gen_id: sender_index,
                    contribution,
                };
                debug!(
                    "{:?} complain {:?} with Error {:?}",
                    self, sender_index, _fault
                );
                let invalid_contribution = serialize(&msg)?;
                self.pending_complain_messages.push(Message::Complaint {
                    key_gen_id: self.our_index,
                    target: sender_index,
                    msg: invalid_contribution,
                });
                return Ok(Vec::new());
            }
        };

        // The row is valid. Encrypt one value for each node and broadcast `Acknowledgment`.
        let mut verified_values = Vec::new();
        let mut enc_values = Vec::new();
        for (index, pk) in self.pub_keys.iter().enumerate() {
            let val = row.evaluate(index + 1);
            let ser_val = serialize(&FieldWrap(val))?;
            enc_values.push(self.encryptor.encrypt(pk, &ser_val)?);
            verified_values.push(ser_val);
        }

        let result = self
            .pub_keys
            .iter()
            .enumerate()
            .map(|(idx, _pk)| Message::Acknowledgment {
                key_gen_id: self.our_index,
                ack: Acknowledgment(
                    sender_index,
                    idx as u64,
                    verified_values[idx].clone(),
                    enc_values.clone(),
                ),
            })
            .collect();
        Ok(result)
    }

    // Handles an `Acknowledgment` message during the `Contribution` phase.
    // When there is an invalidation happens, holds the `Complaint` message till broadcast out
    // when `finalize_contributing` being called.
    fn handle_ack(
        &mut self,
        sender_index: u64,
        ack: Acknowledgment,
    ) -> Result<Vec<Message<S::PublicId>>, Error> {
        if !(self.phase == Phase::Contribute || self.phase == Phase::Combine) {
            return Err(Error::UnexpectedPhase {
                expected: Phase::Contribute,
                actual: self.phase,
            });
        }
        match self.handle_ack_or_fault(sender_index, ack.clone()) {
            Ok(()) => {
                if self.all_contribution_received() {
                    if self.phase == Phase::Combine {
                        self.become_finalization();
                    } else {
                        return self.finalize_contributing_phase();
                    }
                }
            }
            Err(AcknowledgmentFault::MissingContribution) => {
                debug!(
                    "{:?} MissingContribution on Ack not causing a complain, /
                        return with error to trigger an outside cache",
                    self
                );
                return Err(Error::MissingContribution);
            }
            Err(fault) => {
                let msg = Message::<S::PublicId>::Acknowledgment {
                    key_gen_id: sender_index,
                    ack,
                };
                debug!(
                    "{:?} complain {:?} with Error {:?}",
                    self, sender_index, fault
                );

                let invalid_ack = serialize(&msg)?;
                self.pending_complain_messages.push(Message::Complaint {
                    key_gen_id: self.our_index,
                    target: sender_index,
                    msg: invalid_ack,
                });
            }
        }
        Ok(Vec::new())
    }

    pub fn all_contribution_received(&self) -> bool {
        self.pub_keys.len() == self.contribution_trackers.len()
            && self
                .contribution_trackers
                .values()
                .all(|part| part.acks.len() == self.pub_keys.len())
    }

    fn finalize_contributing_phase(&mut self) -> Result<Vec<Message<S::PublicId>>, Error> {
        self.phase = Phase::Complain;

        for non_contributor in self.non_contributors().0 {
            debug!(
                "{:?} complain {:?} for non-contribution during Contribution phase",
                self, non_contributor
            );
            self.pending_complain_messages.push(Message::Complaint {
                key_gen_id: self.our_index,
                target: non_contributor,
                msg: b"Not contributed".to_vec(),
            });
        }
        debug!(
            "{:?} has {:?} complain message and is {:?} ready ({:?} - {:?})",
            self,
            self.pending_complain_messages.len(),
            self.is_ready(),
            self.complete_parts_count(),
            self.threshold,
        );
        // In case of ready, transit into `Finalization` phase.
        if self.is_ready() {
            self.become_finalization();
        }

        self.pending_messags.clear();
        Ok(mem::take(&mut self.pending_complain_messages))
    }

    fn non_contributors(&self) -> (BTreeSet<u64>, BTreeSet<S::PublicId>) {
        let mut non_idxes = BTreeSet::new();
        let mut non_ids = BTreeSet::new();
        let mut missing_times = BTreeMap::new();
        for (idx, id) in self.pub_keys.iter().enumerate() {
            if let Some(contribution_tracker) = self.contribution_trackers.get(&(idx as u64)) {
                if !contribution_tracker.acks.contains(&(idx as u64)) {
                    let times = missing_times.entry(idx).or_insert_with(|| 0);
                    *times += 1;
                    if *times > self.pub_keys.len() / 2 {
                        let _ = non_idxes.insert(idx as u64);
                        let _ = non_ids.insert(id.clone());
                    }
                }
            } else {
                let _ = non_idxes.insert(idx as u64);
                let _ = non_ids.insert(id.clone());
            }
        }
        (non_idxes, non_ids)
    }

    // TODO: So far this function has to be called externally to indicates a completion of the
    //       contribution phase. That is, the owner of the key_gen instance has to wait for a fixed
    //       interval, say an expected timer of 5 minutes, to allow the messages to be exchanged.
    //       May need to be further verified whether there is a better approach.
    pub fn timed_phase_transition<R: RngCore>(
        &mut self,
        rng: &mut R,
    ) -> Result<Vec<Message<S::PublicId>>, Error> {
        debug!("{:?} current phase is {:?}", self, self.phase);
        match self.phase {
            Phase::Contribute => match self.finalize_contributing_phase() {
                Ok(mut messages) => {
                    messages.extend(self.poll_pending_messages(rng));
                    Ok(messages)
                }
                Err(err) => Err(err),
            },
            Phase::Complain=> match self.finalize_complaining_phase(rng) {
                Ok(mut messages) => {
                    messages.extend(self.poll_pending_messages(rng));
                    Ok(messages)
                }
                Err(err) => Err(err),
            },
            Phase::Initialize => Err(Error::UnexpectedPhase {
                expected: Phase::Contribute,
                actual: self.phase,
            }),
            Phase::Combine | Phase::Justify => Err(Error::UnexpectedPhase {
                expected: Phase::Complain,
                actual: self.phase,
            }),

            Phase::Finalize => Ok(Vec::new()),
        }
    }

    // Handles a `Complaint` message.
    fn handle_complaint(
        &mut self,
        sender_index: u64,
        target_index: u64,
        invalid_msg: Vec<u8>,
    ) -> Result<Vec<Message<S::PublicId>>, Error> {
        if self.phase != Phase::Complain {
            return Err(Error::UnexpectedPhase {
                expected: Phase::Complain,
                actual: self.phase,
            });
        }

        let sender_id = self
            .node_id_from_index(sender_index)
            .ok_or(Error::UnknownSender)?;
        let target_id = self
            .node_id_from_index(target_index)
            .ok_or(Error::Unknown)?;

        self.complaints_accumulator
            .add_complaint(sender_id, target_id, invalid_msg);
        Ok(Vec::new())
    }

    fn finalize_complaining_phase<R: RngCore>(
        &mut self,
        rng: &mut R,
    ) -> Result<Vec<Message<S::PublicId>>, Error> {
        let failings = self.complaints_accumulator.finalize_complaining_phase();
        if failings.len() >= self.pub_keys.len() - self.threshold {
            let mut result = BTreeSet::new();
            failings.iter().for_each(|pk| {
                if let Some(index) = self.node_index(pk) {
                    let _ = result.insert(index);
                }
            });
            return Err(Error::TooManyNonVoters(result));
        }

        let mut result = Vec::new();
        // Sending out a Justification message if find self is failed.
        if failings.contains(&self.our_id) {
            result.push(Message::Justification {
                key_gen_id: self.our_index,
                keys_map: self.encryptor.keys_map(),
            });
        }

        // TODO: when there is consensused failing members, we shall transit into Justification
        //       phase to wait for the accused member send us the encryption keys to recover.
        //       However, the accusation could also be `non-contribution`, which disables recovery.
        //       So currently we skip the Justification phase, assuming all the consensused
        //       complained members are really invalid, and transit into the Combination phase to
        //       start a new round of DKG without the complained members.

        if !failings.is_empty() {
            for failing in failings.iter() {
                let _ = self.pub_keys.remove(failing);
            }
            self.our_index = self.node_index(&self.our_id).ok_or(Error::Unknown)?;
        } else if self.is_ready() {
            self.become_finalization();
            return Ok(Vec::new());
        }

        self.phase = Phase::Combine;
        self.contribution_trackers = BTreeMap::new();

        let mut rng = rng_adapter::RngAdapter(&mut *rng);
        let our_contribution = BivarPoly::random(self.threshold, &mut rng);
        let justify_commitment = our_contribution.commitment();
        let encrypt = |(i, pk): (usize, &S::PublicId)| {
            let row = our_contribution.row(i + 1);
            self.encryptor.encrypt(pk, &serialize(&row)?)
        };
        let rows = self
            .pub_keys
            .iter()
            .enumerate()
            .map(encrypt)
            .collect::<Result<Vec<_>, Error>>()?;

        self.pub_keys.iter().enumerate().for_each(|(idx, _pk)| {
            if let Ok(ser_row) = serialize(&our_contribution.row(idx + 1)) {
                result.push(Message::Contribution {
                    key_gen_id: self.our_index,
                    contribution: Contribution {
                        consumer: idx as u64,
                        consumable_commitment: justify_commitment.clone(),
                        ser_row,
                        enc_rows: rows.clone(),
                    },
                });
            }
        });

        Ok(result)
    }

    // Handles a `Justification` message.
    fn handle_justification(
        &mut self,
        _sender_index: u64,
        _keys_map: BTreeMap<S::PublicId, (Key, Iv)>,
    ) -> Result<Vec<Message<S::PublicId>>, Error> {
        // TODO: Need to decide how the justification and recover procedure take out.
        Ok(Vec::new())
    }

    fn become_finalization(&mut self) {
        self.phase = Phase::Finalize;
        self.pending_messags.clear();
        self.pending_complain_messages.clear();
    }

    /// Returns the index of the node, or `None` if it is unknown.
    fn node_index(&self, node_id: &S::PublicId) -> Option<u64> {
        self.pub_keys
            .iter()
            .position(|id| id == node_id)
            .map(|index| index as u64)
    }

    /// Returns the id of the index, or `None` if it is unknown.
    fn node_id_from_index(&self, node_index: u64) -> Option<S::PublicId> {
        for (i, pk) in self.pub_keys.iter().enumerate() {
            if i == node_index as usize {
                return Some(pk.clone());
            }
        }
        None
    }

    /// Returns the number of complete contributions. If this is at least `threshold + 1`, the keys can
    /// be generated, but it is possible to wait for more to increase security.
    fn complete_parts_count(&self) -> usize {
        self.contribution_trackers
            .values()
            .filter(|contribution_tracker| contribution_tracker.is_complete(self.threshold))
            .count()
    }

    // Returns `true` if all contributions are complete to safely generate the new key.
    fn is_ready(&self) -> bool {
        self.complete_parts_count() == self.pub_keys.len()
    }

    /// Returns `true` if in the phase of Finalization.
    pub fn is_finalized(&self) -> bool {
        self.phase == Phase::Finalize
    }

    /// Returns the new secret key share and the public key set.
    pub fn generate_keys(&self) -> Option<(BTreeSet<S::PublicId>, Outcome)> {
        if !self.is_finalized() {
            return None;
        }

        let mut pk_commitment = Poly::zero().commitment();
        let mut sk_val = Fr::zero();
        let is_complete = |contribution_tracker: &&ContributionTracker| contribution_tracker.is_complete(self.threshold);
        for contribution_tracker in self.contribution_trackers.values().filter(is_complete) {
            pk_commitment += contribution_tracker.commitment_from_contribution.row(0);
            let row = Poly::interpolate(contribution_tracker.verified_values.iter().take(self.threshold + 1));
            sk_val.add_assign(&row.evaluate(0));
        }
        let sk = SecretKeyShare::from_mut(&mut sk_val);
        Some((
            self.pub_keys.clone(),
            Outcome::new(pk_commitment.into(), sk),
        ))
    }

    /// This function shall be called when the DKG procedure not reach Finalization phase and before
    /// discarding the instace. It returns potential invalid peers that causing the blocking, if
    /// any and provable.
    pub fn possible_blockers(&self) -> BTreeSet<S::PublicId> {
        let mut result = BTreeSet::new();
        match self.phase {
            Phase::Initialize => {
                for (index, pk) in self.pub_keys.iter().enumerate() {
                    if !self
                        .initalization_accumulator
                        .senders
                        .contains(&(index as u64))
                    {
                        let _ = result.insert(pk.clone());
                    }
                }
            }
            Phase::Contribute => result = self.non_contributors().1,
            Phase::Complain => {
                // Non-voters shall already be returned within the error of the
                // finalize_complaint_phase function call.
            }
            Phase::Justify | Phase::Combine => {
                // As Complaint phase gets completed, it is expected that all nodes are now
                // in these two phases. Hence here a strict rule is undertaken that: any missing
                // vote will be considered as a potential non-voter.
                for contribution_tracker in self.contribution_trackers.values() {
                    for (index, pk) in self.pub_keys.iter().enumerate() {
                        if !contribution_tracker.acks.contains(&(index as u64)) {
                            let _ = result.insert(pk.clone());
                        }
                    }
                }
            }
            Phase::Finalize => {
                // Not blocking
            }
        }
        result
    }

    /// Handles a `Contribution`, returns a `ContributionFault` if it is invalid.
    fn handle_contribution_or_fault(
        &mut self,
        sender_index: u64,
        Contribution {
            consumer,
            consumable_commitment,
            ser_row,
            enc_rows,
        }: Contribution,
    ) -> Result<Option<Poly>, ContributionFault> {
        if enc_rows.len() != self.pub_keys.len() {
            return Err(ContributionFault::RowCount);
        }
        if consumer != self.our_index {
            return Ok(None);
        }
        if let Some(contribution_tracker) = self.contribution_trackers.get(&sender_index) {
            if contribution_tracker.commitment_from_contribution != consumable_commitment {
                return Err(ContributionFault::MultipleContributions);
            }
            return Ok(None); // We already handled this `Contribution` before.
        }
        let ack_row = consumable_commitment.row(self.our_index + 1);
        // Retrieve our own row's commitment, and store the full commitment.
        let _ = self
            .contribution_trackers
            .insert(sender_index, ContributionTracker::new(consumable_commitment));

        let row: Poly = deserialize(&ser_row).map_err(|_| ContributionFault::DeserializeRow)?;
        if row.commitment() != ack_row {
            return Err(ContributionFault::RowAcknowledgment);
        }
        Ok(Some(row))
    }

    /// Handles an acknowledgment.
    fn handle_ack_or_fault(
        &mut self,
        sender_index: u64,
        Acknowledgment(contributor_index, consumer_index, ser_val, values): Acknowledgment,
    ) -> Result<(), AcknowledgmentFault> {
        if values.len() != self.pub_keys.len() {
            return Err(AcknowledgmentFault::ValueCount);
        }
        if consumer_index != self.our_index {
            return Ok(());
        }
        {
            let contribution_tracker = self
                .contribution_trackers
                .get_mut(&contributor_index)
                .ok_or(AcknowledgmentFault::MissingContribution)?;
            if !contribution_tracker.acks.insert(sender_index) {
                return Ok(()); // We already handled this `Acknowledgment` before.
            }
            let our_index = self.our_index;

            let val = deserialize::<FieldWrap<Fr>>(&ser_val)
                .map_err(|_| AcknowledgmentFault::DeserializeValue)?
                .into_inner();
            if contribution_tracker.commitment_from_contribution.evaluate(our_index + 1, sender_index + 1) != G1Affine::one().mul(val)
            {
                return Err(AcknowledgmentFault::ValueAcknowledgment);
            }
            let _ = contribution_tracker.verified_values.insert(sender_index + 1, val);
        }

        {
            let contribution_tracker = self
                .contribution_trackers
                .get_mut(&sender_index)
                .ok_or(AcknowledgmentFault::MissingContribution)?;
            contribution_tracker.enc_values = values;
        }

        Ok(())
    }
}

// https://github.com/rust-lang/rust/issues/52560
// Cannot derive Debug without changing the type parameter
impl<S: SecretId> Debug for KeyGen<S> {
    fn fmt(&self, formatter: &mut Formatter) -> fmt::Result {
        write!(formatter, "KeyGen{{{:?}}}", self.our_id)
    }
}

#[cfg(test)]
impl<S: SecretId> KeyGen<S> {
    /// Returns the list of the final participants.
    pub fn pub_keys(&self) -> &BTreeSet<S::PublicId> {
        &self.pub_keys
    }

    /// Initialize an instance with some pre-defined value, only for testing usage.
    pub fn initialize_for_test(
        our_id: S::PublicId,
        our_index: u64,
        pub_keys: BTreeSet<S::PublicId>,
        threshold: usize,
        phase: Phase,
    ) -> KeyGen<S> {
        assert!(pub_keys.len() >= threshold);
        KeyGen::<S> {
            our_id,
            our_index,
            pub_keys: pub_keys.clone(),
            encryptor: Encryptor::new(&pub_keys),
            contribution_trackers: BTreeMap::new(),
            threshold,
            phase,
            initalization_accumulator: InitializationAccumulator::new(),
            complaints_accumulator: ComplaintsAccumulator::new(pub_keys, threshold),
            pending_complain_messages: Vec::new(),
            pending_messags: Vec::new(),
        }
    }
}

/// `Acknowledgment` faulty entries.
#[derive(
    Clone, Copy, Eq, err_derive::Error, PartialEq, Debug, Serialize, Deserialize, PartialOrd, Ord,
)]
pub enum AcknowledgmentFault {
    /// The number of values differs from the number of nodes.
    #[error(display = "The number of values differs from the number of nodes")]
    ValueCount,
    /// No corresponding Contribution received.
    #[error(display = "No corresponding Contribution received")]
    MissingContribution,
    /// Value decryption failed.
    #[error(display = "Value decryption failed")]
    DecryptValue,
    /// Value deserialization failed.
    #[error(display = "Value deserialization failed")]
    DeserializeValue,
    /// Value doesn't match the ack.
    #[error(display = "Value doesn't match the ack")]
    ValueAcknowledgment,
}

/// `Contribution` faulty entries.
#[derive(
    Clone, Copy, Eq, err_derive::Error, PartialEq, Debug, Serialize, Deserialize, PartialOrd, Ord,
)]
pub enum ContributionFault {
    /// The number of rows differs from the number of nodes.
    #[error(display = "The number of rows differs from the number of nodes")]
    RowCount,
    /// Received multiple different Part messages from the same sender.
    #[error(display = "Received multiple different Contribution messages from the same contributor")]
    MultipleContributions,
    /// Could not decrypt our row in the Contribution message.
    #[error(display = "Could not decrypt our row in the Contribution message")]
    DecryptRow,
    /// Could not deserialize our row in the Contribution message.
    #[error(display = "Could not deserialize our row in the Contribution message")]
    DeserializeRow,
    /// Row does not match the ack.
    #[error(display = "Row does not match the ack")]
    RowAcknowledgment,
}
