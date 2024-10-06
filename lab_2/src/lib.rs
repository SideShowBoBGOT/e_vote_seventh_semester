extern crate derive_more;

use num_bigint::BigUint;
use num_traits::ToPrimitive;

pub fn convert_to_bytes<E>(i: &[BigUint]) -> Result<Vec<u8>, E>
where
    E: From<BigUint>
{
    i.iter()
        .try_fold(Vec::new(), |mut acc, unit| {
            unit.to_u8().ok_or_else(|| {
                E::from(unit.clone())
            }).map(|byte| {
                acc.push(byte);
                acc
            })
        })
}

mod rsa {
    use std::ops::Rem;
    use derive_more::Deref;
    use getset::Getters;
    use lazy_static::lazy_static;
    use num_bigint::{BigUint, RandBigInt};
    use num_traits::{One, Zero};
    use rand::Rng;
    use serde::{Deserialize, Serialize};
    use thiserror::Error;

    const MIN_GENERATED_NUMBER: u32 = u16::MAX as u32;
    const MAX_GENERATED_NUMBER: u32 = u32::MAX;

    pub fn generate_num() -> BigUint {
        BigUint::from(rand::thread_rng().gen_range(MIN_GENERATED_NUMBER..MAX_GENERATED_NUMBER))
    }

    fn generate_num_by_condition(predicate: fn(&BigUint) -> bool) -> BigUint {
        loop {
            let num = generate_num();
            if predicate(&num) {
                return num;
            }
        }
    }

    lazy_static! {
        static ref TWO: BigUint = BigUint::from(2u32);
    }

    fn is_prime(n: &BigUint) -> bool {
        if *n < *TWO {
            return false;
        }
        let mut i = TWO.clone();
        let n_sqrt = n.sqrt();
        while i < n_sqrt {
            if n.clone().rem(&i).is_zero() {
                return false;
            }
            i += BigUint::one();
        }
        true
    }

    fn generate_prime() -> BigUint {
        generate_num_by_condition(is_prime)
    }

    lazy_static! {
        pub static ref PUBLIC_NUMBER: BigUint = BigUint::from(65537u32);
    }

    #[derive(Debug, Clone, Deref, Serialize, Deserialize)]
    pub struct ProductNumber(BigUint);

    #[derive(Debug, Getters)]
    pub struct PrivateKeyRef<'a> {
        private_number: &'a BigUint,
        #[get = "pub with_prefix"]
        product_number: &'a ProductNumber
    }

    #[derive(Debug, Getters)]
    pub struct PublicKeyRef<'a> {
        #[get = "pub with_prefix"]
        product_number: &'a ProductNumber
    }

    #[derive(Debug, Clone, Getters)]
    pub struct KeyPair {
        #[get = "pub with_prefix"]
        product_number: ProductNumber,
        private_number: BigUint,
    }

    impl Default for KeyPair {
        fn default() -> Self {
            DEFAULT_KEY_PAIR.clone()
        }
    }

    lazy_static! {
        pub static ref DEFAULT_KEY_PAIR: KeyPair = KeyPair::new();
    }

    #[derive(Error, Debug)]
    #[error("Base {base} is bigger or equal to {modulus}")]
    pub struct ModPowError {
        base: BigUint,
        modulus: BigUint,
    }

    fn modpow(base: &BigUint, exp: &BigUint, modulus: &BigUint) -> Result<BigUint, ModPowError> {
        if base >= modulus {
            Err(ModPowError{base: base.clone(), modulus: modulus.clone()})
        } else {
            Ok(base.modpow(exp, modulus))
        }
    }

    impl KeyPair {
        pub fn new() -> Self {
            loop {
                let p = generate_prime();
                let q = generate_prime();
                let n = ProductNumber(p.clone() * q.clone());
                let phi = (p.clone() - BigUint::one()) * (q.clone() - BigUint::one());
                if *PUBLIC_NUMBER < phi {
                    if let Some(d) = PUBLIC_NUMBER.modinv(&phi) {
                        return Self { product_number: n, private_number: d }
                    }
                }
            }
        }

        pub fn get_private_key_ref(&self) -> PrivateKeyRef {
            PrivateKeyRef { product_number: &self.product_number, private_number: &self.private_number }
        }

        pub fn get_public_key_ref(&self) -> PublicKeyRef {
            PublicKeyRef { product_number: &self.product_number }
        }
    }

    pub trait KeyRef {
        fn get_parts(&self) -> (&BigUint, &ProductNumber);
    }

    impl<'a> KeyRef for PrivateKeyRef<'a> {
        fn get_parts(&self) -> (&BigUint, &ProductNumber) {
            (self.private_number, self.product_number)
        }
    }

    impl<'a> KeyRef for PublicKeyRef<'a> {
        fn get_parts(&self) -> (&BigUint, &ProductNumber) {
            (&PUBLIC_NUMBER, self.product_number)
        }
    }

    #[derive(Error, Debug)]
    #[error(transparent)]
    pub struct CipherDataError(#[from] ModPowError);

    pub fn cipher_data_biguint(key: &impl KeyRef, mut data: Vec<BigUint>, ) -> Result<Vec<BigUint>, CipherDataError> {
        let (part, product_number) = key.get_parts();
        for c in &mut data {
            *c = modpow(c, part, product_number)?;
        }
        Ok(data)
    }

    pub fn cipher_data_u8(key: &impl KeyRef, data: &[u8]) -> Result<Vec<BigUint>, CipherDataError> {
        let (part, product_number) = key.get_parts();
        data.iter().try_fold(Vec::new(), |mut acc, byte| {
            acc.push(modpow(&BigUint::from(*byte), part, product_number)?);
            Ok(acc)
        })
    }

    pub struct ApplyBlindingOps {
        mask_multiplicative: BigUint,
        product_number: ProductNumber
    }

    impl ApplyBlindingOps {
        pub fn apply(&self, data: &[u8]) -> Vec<BigUint> {
            data.iter().map(|byte| {
                let m: BigUint = (*byte).into();
                (m * &self.mask_multiplicative) % &self.product_number.0
            })
                .collect::<Vec<_>>()
        }
    }

    #[derive(Serialize, Deserialize)]
    pub struct UnapplyBlindingOps {
        mask_multiplicative_inverse: BigUint,
        product_number: ProductNumber
    }

    impl UnapplyBlindingOps {
        pub fn apply(&self, mut data: Vec<BigUint>) -> Vec<BigUint> {
            for unit in &mut data {
                *unit *= &self.mask_multiplicative_inverse;
                *unit %= &self.product_number.0;
            }
            data
        }
    }

    pub fn create_blinding_ops(public_key_ref: &PublicKeyRef) -> (ApplyBlindingOps, UnapplyBlindingOps) {
        let (r, r_inv) = loop {
            let r = rand::thread_rng().gen_biguint_below(public_key_ref.product_number);
            if let Some(r_inv) = r.modinv(public_key_ref.product_number) {
                break (r, r_inv);
            }
        };

        let (e, n) = public_key_ref.get_parts();
        let mask_multiplicative = modpow(&r, e, n).unwrap();

        (
            ApplyBlindingOps { mask_multiplicative, product_number: n.clone() },
            UnapplyBlindingOps { mask_multiplicative_inverse: r_inv, product_number: n.clone() }
        )
    }

    #[cfg(test)]
    mod tests {
        use num_traits::ToPrimitive;
        use super::{cipher_data_biguint, cipher_data_u8, create_blinding_ops, CipherDataError, KeyPair};

        #[test]
        fn test_blinding() -> Result<(), CipherDataError> {
            let receiver = KeyPair::new();

            let message = "message";

            let (apply_ops, unapply_ops) = {
                create_blinding_ops(&receiver.get_public_key_ref())
            };

            let original_data = {
                let unblinded_signed_data = {
                    let signed_blinded_data = {
                        let unciphered_blinded_data = {
                            let ciphered_blinded_data = {
                                let blinded_data = apply_ops.apply(message.as_bytes());
                                cipher_data_biguint(
                                    &receiver.get_public_key_ref(), blinded_data
                                )?
                            };
                            cipher_data_biguint(
                                &receiver.get_private_key_ref(), ciphered_blinded_data
                            )?
                        };
                        cipher_data_biguint(
                            &receiver.get_private_key_ref(), unciphered_blinded_data
                        )?
                    };
                    unapply_ops.apply(signed_blinded_data)
                };

                cipher_data_biguint(
                    &receiver.get_public_key_ref(), unblinded_signed_data
                )?
            };

            let original_bytes = original_data.into_iter()
                .map(|e| {
                    e.to_u8().unwrap()
                }).collect::<Vec<_>>();

            let original_message = String::from_utf8(original_bytes).unwrap();

            assert_eq!(original_message, message);
            println!("{}", original_message);
            Ok(())
        }

        #[test]
        fn test_ciphering() {
            let r = KeyPair::new();
            let message = "message";
            let ciphered_data = cipher_data_u8(
                &r.get_public_key_ref(), message.as_bytes()
            ).unwrap();
            let deciphered_data = cipher_data_biguint(
                &r.get_private_key_ref(), ciphered_data
            ).unwrap().into_iter().map(|e| e.to_u8().unwrap()).collect();
            let deciphered_message = String::from_utf8(deciphered_data).unwrap();
            assert_eq!(deciphered_message, message);
            println!("{}", deciphered_message);
        }
    }
}


mod voter {
    use std::num::NonZeroUsize;
    use derive_more::From;
    use getset::Getters;
    use num_bigint::BigUint;
    use rand::prelude::SliceRandom;
    use serde::{Deserialize, Serialize};
    use thiserror::Error;
    use crate::{convert_to_bytes, rsa};
    use crate::rsa::{cipher_data_biguint, cipher_data_u8, CipherDataError, UnapplyBlindingOps};

    #[derive(Serialize, Deserialize)]
    pub(crate) struct PacketsData {
        pub blinded_candidate_id_vec_vec: Vec<BlindedCandidateIdVec>,
        pub unapply_blind_ops: rsa::UnapplyBlindingOps,
    }

    #[derive(
        Serialize, Deserialize, Clone,
        Default, PartialEq, Eq, Hash, Debug
    )]
    pub struct VoterId(pub BigUint);

    #[derive(Default, Getters)]
    #[getset(get = "pub with_prefix")]
    pub struct Voter {
        // key_pair: rsa::KeyPair,
        id: VoterId
    }

    #[derive(Serialize, Clone)]
    struct CandidateIdRef<'a> {
        candidate: &'a str,
        id: &'a VoterId
    }

    #[derive(Serialize, Deserialize, Getters, Default, Clone)]
    #[getset(get = "pub with_prefix")]
    pub struct CandidateId {
        candidate: String,
        id: VoterId
    }

    #[derive(Deserialize, Default, Clone)]
    pub struct CandidateIdVec(pub Vec<CandidateId>);

    #[derive(Serialize, Default, Clone)]
    pub struct CandidateIdRefVec<'a>(Vec<CandidateIdRef<'a>>);

    #[derive(Serialize, Deserialize, Clone, Default)]
    pub struct SerializedCandidateIdVec(pub Vec<u8>);

    #[derive(Serialize, Deserialize, Default, Clone)]
    pub struct BlindedCandidateIdVec(pub Vec<BigUint>);

    #[derive(Error, Debug)]
    pub enum ProducePacketsError {
        #[error("Failed to serialize candidate_id: {0}")]
        SerializedCandidateId(bincode::Error),
        #[error("Failed to serialize packets_data: {0}")]
        SerializePackets(bincode::Error),
        #[error("Failed to cipher packets_data: {0}")]
        CipherPacketsData(#[from] CipherDataError),
    }

    #[derive(Error, Debug, From)]
    #[error("Failed to convert unciphered data to bytes")]
    pub struct UncipheredConvertToBytesError(BigUint);

    #[derive(Error, Debug)]
    pub enum VoteError {
        #[error("Failed to uncipher vote: {0}")]
        FailedUncipherVote(#[from] CipherDataError),
        #[error(transparent)]
        FailedUncipheredConvertToBytes(#[from] UncipheredConvertToBytesError),
        #[error("Failed to deserialize candidate id vec: {0}")]
        FailedDeserializeCandidateIdVec(bincode::Error),
        #[error("Candidate id vec is empty")]
        CandidateIdVecIsEmpty,
        #[error("Failed serialize candidate id")]
        FailedSerializeCandidateId(bincode::Error),
        #[error("Failed serialize candidate id")]
        FailedCipherCandidateId(CipherDataError)
    }

    impl Voter {
        pub fn new() -> Self {
            Self {
                // key_pair: rsa::KeyPair::new(),
                id: VoterId(rsa::generate_num())
            }
        }

        pub fn produce_packets<'a>(
            &'a self,
            candidate_id_vec_number: NonZeroUsize,
            candidates: impl Iterator<Item=&'a String> + Clone,
            cec_public_key: &'a rsa::PublicKeyRef
        ) -> Result<Vec<BigUint>, ProducePacketsError> {
            let ser_candidate_id_vec = {
                let candidate_id_pairs = CandidateIdRefVec(
                    candidates.clone().map(
                        |c| CandidateIdRef {candidate: c.as_ref(), id: &self.id }
                    ).collect::<Vec<_>>()
                );
                bincode::serialize(&candidate_id_pairs)
                    .map_err(ProducePacketsError::SerializedCandidateId)
                    .map(|serialized_candidate_ids| vec![
                        SerializedCandidateIdVec(serialized_candidate_ids);
                        candidate_id_vec_number.get()
                    ])?
            };
            let (apply_blind_ops, unapply_blind_ops) = {
                rsa::create_blinding_ops(cec_public_key)
            };
            let blinded_candidate_id_vec_vec = {
                ser_candidate_id_vec.into_iter().map(|candidate_id| {
                    BlindedCandidateIdVec(apply_blind_ops.apply(&candidate_id.0))
                }).collect::<Vec<_>>()
            };
            let packets_data = PacketsData{ blinded_candidate_id_vec_vec, unapply_blind_ops };
            let serialized_packet = bincode::serialize(&packets_data)
                .map_err(ProducePacketsError::SerializePackets)?;
            rsa::cipher_data_u8(cec_public_key, &serialized_packet).map_err(Into::into)
        }

        pub fn accept_signed_packet_and_vote(
            &self,
            signed_blinded_vote: Vec<BigUint>,
            unapply_blinding_ops: UnapplyBlindingOps,
            cec_public_key: &rsa::PublicKeyRef
        ) -> Result<Vec<BigUint>, VoteError> {
            let signed_vote = unapply_blinding_ops.apply(signed_blinded_vote);
            cipher_data_biguint(cec_public_key, signed_vote)
                .map_err(VoteError::FailedUncipherVote)
                .and_then(|data|
                    convert_to_bytes::<UncipheredConvertToBytesError>(&data)
                        .map_err(VoteError::from)
                )
                .and_then(|byte_data|
                    bincode::deserialize::<CandidateIdVec>(&byte_data)
                        .map_err(VoteError::FailedDeserializeCandidateIdVec)
                )
                .and_then(|candidate_id_vec| {
                    candidate_id_vec.0.choose(&mut rand::thread_rng())
                        .ok_or(VoteError::CandidateIdVecIsEmpty)
                        .and_then(|candidate_id| {
                            bincode::serialize(&candidate_id)
                                .map_err(VoteError::FailedSerializeCandidateId)
                        })
                })
                .and_then(|serialized_candidate_id| {
                    cipher_data_u8(cec_public_key, &serialized_candidate_id)
                        .map_err(VoteError::FailedCipherCandidateId)
                })
        }
    }
}

mod cec {
    use std::collections::HashMap;
    use derive_more::From;
    use num_bigint::BigUint;
    use num_integer::Integer;
    use thiserror::Error;
    use crate::{convert_to_bytes, rsa, voter};
    use crate::rsa::{CipherDataError, UnapplyBlindingOps};
    use crate::voter::VoterId;

    pub struct Cec {
        candidates: HashMap<String, u64>,
        voters_state: HashMap<voter::VoterId, VoterState>,
        key_pair: rsa::KeyPair,
    }

    #[derive(Error, Debug, From)]
    #[error("Failed to convert unciphered to bytes: {0}")]
    pub struct ConvertUncipheredToBytesError(BigUint);

    #[derive(Error, Debug)]
    pub enum VoteError {
        #[error("Failed to decipher vote: {0}")]
        FailedDecipherVote(CipherDataError),
        #[error(transparent)]
        ConvertUncipheredToBytes(#[from] ConvertUncipheredToBytesError),
        #[error("Failed to deserialize candidate id vec: {0}")]
        FailedToDeserializeCandidateId(#[from] bincode::Error),
        #[error("Voter id is absent: {0:?}")]
        VoterIdAbsent(VoterId),
        #[error("Voter has invalid state: {0:?}")]
        VoterInvalidState(VoterState),
        #[error("Invalid candidate: {0}")]
        InvalidCandidate(String),
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum CanVoteState {
        NotRegistered,
        Registered,
        Voted
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum VoterState {
        CanVote(CanVoteState),
        CanNotVote,
    }

    #[derive(Error, Debug, From)]
    #[error("Failed to convert deciphered packet to byte data: {0}")]
    pub struct ConvertToByteDataError(BigUint);

    #[derive(Error, Debug, From)]
    #[error("Failed to convert unsigned candidate_id_vec to byte data: {0}")]
    pub struct ConvertUnsignedCandidateIdVecToByteDataError(BigUint);

    #[derive(Error, Debug)]
    pub enum ConsumePacketsError {
        #[error("Failed to decipher packet: {0}")]
        FailedToDecipherPacket(rsa::CipherDataError),
        #[error(transparent)]
        FailedConvertToByteData(#[from] ConvertToByteDataError),
        #[error("Failed to deserialize packets_data: {0}")]
        FailedToDeserializePackets(bincode::Error),
        #[error("Failed to sign candidate_id_vec: {0}")]
        FailedSignCandidateIdVec(rsa::CipherDataError),
        #[error("Packet data is empty")]
        PacketDataIsEmpty,
        #[error("Failed to unsign candidate_id: {0}")]
        FailedUnsignCandidateIdVec(rsa::CipherDataError),
        #[error(transparent)]
        FailedConvertUnsignedCandidateIdVecToByteData(
            #[from] ConvertUnsignedCandidateIdVecToByteDataError
        ),
        #[error("Failed to deserialize candidate_id: {0}")]
        FailedDeserializedCandidateId(bincode::Error),
        #[error(transparent)]
        CheckCandidateIdError(#[from] CheckCandidateIdError),
    }

    #[derive(Error, Debug)]
    pub enum CheckCandidateIdError {
        #[error("Invalid candidate: {0}")]
        InvalidCandidateError(String),
        #[error("Invalid voter id: {0:?}")]
        InvalidVoterId(voter::VoterId),
        #[error("Invalid voter state: {0:?}")]
        InvalidVoterState(VoterState),
        #[error("Ids are not the same: {0:?} != {1:?}")]
        IdsAreNotTheSame(voter::VoterId, voter::VoterId),
        #[error("Real: {0}, packet: {1}")]
        CandidatesListLenNotMatch(usize, usize)
    }

    fn check_packet<'a>(
        candidate_id_vec_vec: &'a [voter::CandidateIdVec],
        candidates: &'a HashMap<String, u64>,
        voters_state: &'a HashMap<voter::VoterId, VoterState>,
    ) -> Result<voter::VoterId, CheckCandidateIdError> {
        for candidate_id_vec in candidate_id_vec_vec.iter() {
            if candidate_id_vec.0.len() != candidates.len() {
                return Err(
                    CheckCandidateIdError::CandidatesListLenNotMatch(
                        candidates.len(), candidate_id_vec.0.len()
                    )
                )
            }
            for (candidate_id, true_candidate) in candidate_id_vec.0.iter().zip(candidates.keys()) {
                if candidate_id.get_candidate() != true_candidate {
                    return Err(CheckCandidateIdError::InvalidCandidateError(candidate_id.get_candidate().clone()));
                }
                if let Some(voter_state) = voters_state.get(candidate_id.get_id()) {
                    match voter_state {
                        VoterState::CanVote(can_vote_state) => {
                            match can_vote_state {
                                CanVoteState::NotRegistered => (),
                                _ => return Err(CheckCandidateIdError::InvalidVoterState(voter_state.clone())),
                            }
                        },
                        VoterState::CanNotVote => {
                            return Err(CheckCandidateIdError::InvalidVoterState(voter_state.clone()))
                        }
                    }
                } else {
                    return Err(CheckCandidateIdError::InvalidVoterId(candidate_id.get_id().clone()))
                }
            }
        }

        let first = &candidate_id_vec_vec[0].0.first().unwrap();
        for candidate_id_vec in candidate_id_vec_vec.iter() {
            for candidate_id in candidate_id_vec.0.iter() {
                if first.get_id() != candidate_id.get_id() {
                    return Err(CheckCandidateIdError::IdsAreNotTheSame(
                        first.get_id().clone(), candidate_id.get_id().clone()
                    ))
                }
            }
        }
        Ok(first.get_id().clone())
    }

    impl Cec {
        pub fn new(
            candidates: impl Iterator<Item=String>,
            voters_state: HashMap<voter::VoterId, VoterState>
        ) -> Self {
            Self {
                candidates: HashMap::from_iter(
                    candidates.map(|c| (c, 0u64))
                ),
                voters_state,
                key_pair: rsa::KeyPair::new()
            }
        }

        pub fn consume_packets(
            &mut self,
            ciphered_data: Vec<BigUint>
        ) -> Result<(Vec<BigUint>, UnapplyBlindingOps), ConsumePacketsError> {
            let (unapply_blind_ops, mut signed_blinded_candidate_id_vec_vec) = {
                let packet_data: voter::PacketsData = {
                    let deciphered_byte_data = {
                        let deciphered_data = rsa::cipher_data_biguint(
                            &self.key_pair.get_private_key_ref(), ciphered_data
                        ).map_err(|err| {
                            ConsumePacketsError::FailedToDecipherPacket(err)
                        })?;
                        convert_to_bytes::<ConvertToByteDataError>(&deciphered_data)?
                    };
                    bincode::deserialize(&deciphered_byte_data)
                        .map_err(ConsumePacketsError::FailedToDeserializePackets)?
                };
                (
                    packet_data.unapply_blind_ops,
                    packet_data.blinded_candidate_id_vec_vec
                        .into_iter()
                        .try_fold(
                            Vec::new(),
                            |mut acc, candidate_id_vec| {
                                acc.push(
                                    rsa::cipher_data_biguint(
                                        &self.key_pair.get_private_key_ref(),
                                        candidate_id_vec.0
                                    )?
                                );
                                Ok(acc)
                            }
                        )
                        .map_err(ConsumePacketsError::FailedSignCandidateIdVec)?
                )
            };

            if signed_blinded_candidate_id_vec_vec.is_empty() {
                Err(ConsumePacketsError::PacketDataIsEmpty)
            } else {
                let last = signed_blinded_candidate_id_vec_vec.pop().unwrap();
                let unblinded_signed_candidate_id_vec_vec = signed_blinded_candidate_id_vec_vec
                    .into_iter()
                    .map(
                        |candidate_id_vec| unapply_blind_ops.apply(candidate_id_vec)
                    )
                    .collect::<Vec<_>>();
                let check_candidate_id_vec_vec = {
                    unblinded_signed_candidate_id_vec_vec.into_iter()
                        .try_fold(
                            Vec::new(),
                            |mut acc, signed_candidate_id_vec| {
                                rsa::cipher_data_biguint(
                                    &self.key_pair.get_public_key_ref(),
                                    signed_candidate_id_vec
                                ).map_err(ConsumePacketsError::FailedUnsignCandidateIdVec)
                                    .and_then(|ser_big_candidate_id_vec| {
                                        convert_to_bytes::<ConvertUnsignedCandidateIdVecToByteDataError>(&ser_big_candidate_id_vec)
                                            .map_err(Into::into)
                                    })
                                    .and_then(|ser_candidate_id_vec| {
                                        bincode::deserialize::<voter::CandidateIdVec>(&ser_candidate_id_vec)
                                            .map_err(ConsumePacketsError::FailedDeserializedCandidateId)
                                    })
                                    .map(|candidate_id_vec| {
                                        acc.push(candidate_id_vec);
                                        acc
                                    })
                            }
                        )?
                };
                let voter_id = check_packet(&check_candidate_id_vec_vec, &self.candidates, &self.voters_state)?;
                *self.voters_state.get_mut(&voter_id).unwrap() = VoterState::CanVote(CanVoteState::Registered);
                Ok((last, unapply_blind_ops))
            }
        }

        pub fn process_vote(&mut self, vote: Vec<BigUint>) -> Result<(), VoteError> {
            rsa::cipher_data_biguint(&self.key_pair.get_private_key_ref(), vote)
                .map_err(VoteError::FailedDecipherVote)
                .and_then(|ser_big_candidate_id_vec| {
                    convert_to_bytes::<ConvertUncipheredToBytesError>(&ser_big_candidate_id_vec)
                        .map_err(VoteError::from)
                })
                .and_then(|ser_candidate_id_vec| {
                    bincode::deserialize::<voter::CandidateId>(&ser_candidate_id_vec)
                        .map_err(VoteError::FailedToDeserializeCandidateId)
                })
                .and_then(|candidate_id| {
                    self.voters_state.get_mut(candidate_id.get_id())
                        .ok_or_else(|| VoteError::VoterIdAbsent(candidate_id.get_id().clone()))
                        .and_then(|voter_state| {
                            if *voter_state != VoterState::CanVote(CanVoteState::Registered) {
                                Err(VoteError::VoterInvalidState(voter_state.clone()))
                            } else {
                                self.candidates.get_mut(candidate_id.get_candidate())
                                    .ok_or_else(|| VoteError::InvalidCandidate(candidate_id.get_candidate().clone()))
                                    .map(|votes_number| {
                                        votes_number.inc();
                                        *voter_state = VoterState::CanVote(CanVoteState::Voted);
                                    })
                            }
                        })
                })
        }

        pub fn get_candidates(&self) -> &HashMap<String, u64> {
            &self.candidates
        }

        pub fn get_public_key(&self) -> rsa::PublicKeyRef {
            self.key_pair.get_public_key_ref()
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::num::NonZeroUsize;
    use crate::{cec, voter};

    #[test]
    fn test_vote() {
        let mut voters = (0..10).into_iter().map(|_| voter::Voter::new())
            .collect::<Vec<_>>();

        let mut cec = cec::Cec::new(
            (0..10).into_iter().map(|i| format!("Candidate {}", i)),
            HashMap::from_iter(voters.iter().map(|v| (
                v.get_id().clone(), cec::VoterState::CanVote(cec::CanVoteState::NotRegistered)))
            )
        );

        for voter in &mut voters {
            let packet = voter.produce_packets(
                NonZeroUsize::new(10).unwrap(), cec.get_candidates().keys(), &cec.get_public_key()
            ).unwrap();
            let signed_candidate_id_vec = cec.consume_packets(packet).unwrap();
            let ciphered_vote = voter.accept_signed_packet_and_vote(
                signed_candidate_id_vec.0, signed_candidate_id_vec.1, &cec.get_public_key()
            ).unwrap();
            cec.process_vote(ciphered_vote).unwrap()
        }

        for el in cec.get_candidates() {
            println!("{:?}", el);
        }
    }
}