extern crate derive_more;

use serde::{Deserialize, Serialize};

mod rsa {
    use std::ops::Rem;
    use derive_more::Deref;
    use getset::Getters;
    use lazy_static::lazy_static;
    use num_bigint::{BigUint};
    use num_traits::{One, ToBytes, Zero};
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

    #[derive(Debug, Clone, Deref)]
    pub struct ProductNumber(BigUint);

    // #[derive(Debug, Clone, Getters)]
    // pub struct PrivateKey {
    //     private_number: BigUint,
    //     #[get = "pub with_prefix"]
    //     product_number: ProductNumber
    // }

    #[derive(Debug, Getters)]
    pub struct PrivateKeyRef<'a> {
        private_number: &'a BigUint,
        #[get = "pub with_prefix"]
        product_number: &'a ProductNumber
    }

    // #[derive(Debug, Clone, Getters)]
    // pub struct PublicKey {
    //     #[get = "pub with_prefix"]
    //     product_number: ProductNumber
    // }

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

    fn quad_fold_hash(n: &ProductNumber, data: &[u8]) -> BigUint {
        data.iter().fold(BigUint::zero(), |acc, x| {
            (acc + BigUint::from(*x)).modpow(&TWO, &n.0)
        })
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

    fn calc_chunk_size(product_number: &ProductNumber) -> usize {
        let bits = product_number.bits() as usize;
        assert!(bits >= 2);
        bits - 1
    }

    pub fn cipher_data(key: &impl KeyRef, data: &[u8]) -> Vec<BigUint> {
        let (part, product_number) = key.get_parts();
        let chunk_size = calc_chunk_size(product_number);
        data.chunks(chunk_size)
            .map(|data_chunk| {
                let val = BigUint::from_bytes_le(data_chunk);
                let c = val.modpow(part, product_number);
                c
            })
            .collect::<Vec<_>>()
    }

    pub fn decipher_data(key: &impl KeyRef, ciphered_data: &[BigUint]) -> Vec<u8> {
        let (part, product_number) = key.get_parts();
        let chunk_size = calc_chunk_size(product_number);
        ciphered_data.iter().fold(Vec::new(), |mut acc, chunk| {
            let val = chunk.modpow(part, product_number);
            let bytes = val.to_bytes_le();
            acc.extend(bytes);
            acc
        })
    }

    #[derive(Serialize, Deserialize)]
    pub struct BlindKey(BigUint);
    #[derive(Error, Debug)]
    #[error("Failed to generate blind key")]
    pub struct BlindKeyError();

    impl BlindKey {
        pub fn new(product_number: &ProductNumber) -> Result<Self, BlindKeyError> {
            BigUint::one().modinv(product_number).map(Self)
                .ok_or(BlindKeyError())
        }
    }

    pub struct ApplyBlindingOps {
        mask_multiplicative: BigUint,
        chunk_size: usize,
    }

    impl ApplyBlindingOps {
        pub fn new(blind_key: &BlindKey, product_number: &ProductNumber) -> Self {
            let mask_multiplicative = {
                blind_key.0.modpow(&PUBLIC_NUMBER, product_number)
            };
            let chunk_size = calc_chunk_size(product_number);
            Self { mask_multiplicative, chunk_size }
        }
        pub fn apply(&self, data: &[u8]) -> Vec<BigUint> {
            data.chunks(self.chunk_size)
                .map(|data_chunk| {
                    BigUint::from_bytes_le(data_chunk) * self.mask_multiplicative.clone()
                })
                .collect::<Vec<_>>()
        }
    }

    // mask_multiplicative_inverse
    pub struct UnapplyBlindingOps(BigUint);

    #[derive(Error, Debug)]
    #[error("Failed to cal modular multiplicative inverse")]
    pub struct UnapplyBlindingOpsError();

    impl UnapplyBlindingOps {
        pub fn new(
            blind_key: &BlindKey,
            product_number: &ProductNumber
        ) -> Result<Self, UnapplyBlindingOpsError> {
            blind_key.0.modinv(product_number).map(Self)
                .ok_or(UnapplyBlindingOpsError())
        }

        pub fn apply(&self, data: &[BigUint]) -> Vec<u8> {
            data.iter().fold(Vec::new(), |mut acc, chunk| {
                acc.extend((chunk * self.0.clone()).to_bytes_le() );
                acc
            })    
        }
    }

    #[cfg(test)]
    mod tests {
        use super::{
            cipher_data, decipher_data, ApplyBlindingOps,
            BlindKey, KeyPair, UnapplyBlindingOps
        };

        #[test]
        fn test_ciphering() {
            let r = KeyPair::new();
            let message = "message";
            let ciphered_data = cipher_data(
                &r.get_public_key_ref(), message.as_bytes()
            );
            let deciphered_data = decipher_data(
                &r.get_private_key_ref(), &ciphered_data
            );
            let deciphered_message = String::from_utf8(deciphered_data).unwrap();
            assert_eq!(deciphered_message, message);
            println!("{}", deciphered_message);
        }

        #[test]
        fn test_blinding() {
            let sender = KeyPair::new();
            let receiver = KeyPair::new();
            let message = "message";
            let blind_key = {
                BlindKey::new(sender.get_product_number()).unwrap()
            };
            let apply_blinding_ops = ApplyBlindingOps::new(&blind_key, receiver.get_product_number());
            let unapply_blinding_ops = {
                UnapplyBlindingOps::new(&blind_key, receiver.get_product_number()).unwrap()
            };

            let blinded_data = apply_blinding_ops.apply(message.as_bytes());
            let unblinded_data = unapply_blinding_ops.apply(&blinded_data);
            let unblined_message = String::from_utf8(unblinded_data).unwrap();

            assert_eq!(unblined_message, message);
            println!("{}", unblined_message);
        }
    }
}

mod voter {
    use std::num::NonZeroUsize;
    use getset::Getters;
    use num_bigint::BigUint;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use thiserror::Error;
    use crate::rsa;
    use crate::rsa::BlindKeyError;

    pub const PACKETS_NUMBER: usize = 10;

    #[derive(Getters, Serialize, Deserialize)]
    #[getset(get = "pub with_prefix")]
    pub(crate) struct PacketsData {
        blinded_candidate_id_vec_vec: Vec<BlindedCandidateIdVec>,
        blind_key: rsa::BlindKey,
    }

    #[derive(Getters, Clone)]
    #[getset(get = "pub with_prefix")]
    pub struct VoteData {
        encrypted_gamming_key: BigUint,
        rsa_signature: BigUint,
        gammed_vote: Vec<u8>
    }

    #[derive(
        Serialize, Deserialize, Clone,
        Default, PartialEq, Eq, Hash, Debug
    )]
    pub struct VoterId(pub BigUint);

    #[derive(Default, Getters)]
    #[getset(get = "pub with_prefix")]
    pub struct Voter {
        key_pair: rsa::KeyPair,
        id: VoterId
    }

    #[derive(Serialize, Clone)]
    struct CandidateIdRef<'a> {
        candidate: &'a str,
        id: &'a VoterId
    }

    #[derive(Deserialize, Getters, Default, Clone)]
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
        FailedSerializedCandidateId(bincode::Error),
        #[error(transparent)]
        BlindKeyError(#[from] BlindKeyError),
        #[error("Failed to serialize packets_data: {0}")]
        FailedToSerializePackets(bincode::Error),
    }

    impl Voter {
        pub fn new() -> Self {
            Self {
                key_pair: rsa::KeyPair::new(),
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
                    .map_err(ProducePacketsError::FailedSerializedCandidateId)
                    .map(|serialized_candidate_ids| vec![
                        SerializedCandidateIdVec(serialized_candidate_ids);
                        candidate_id_vec_number.get()
                    ])?
            };
            let blind_key = {
                rsa::BlindKey::new(self.key_pair.get_product_number())
                    .map_err(ProducePacketsError::BlindKeyError)?
            };
            let apply_blinding_ops = rsa::ApplyBlindingOps::new(
                &blind_key, cec_public_key.get_product_number()
            );
            let blinded_candidate_id_vec_vec = {
                ser_candidate_id_vec.into_iter().map(|candidate_id| {
                    BlindedCandidateIdVec(apply_blinding_ops.apply(&candidate_id.0))
                }).collect::<Vec<_>>()
            };
            let packets_data = PacketsData{ blinded_candidate_id_vec_vec, blind_key};
            bincode::serialize(&packets_data)
                .map(|packet_data| {
                    rsa::cipher_data(cec_public_key, &packet_data)
                })
                .map_err(|err| ProducePacketsError::FailedToSerializePackets(err))
        }

        pub fn accept_signed_packet_and_vote(
            &self,
            ciphered_blinded_vote: &[BigUint],
            cec_public_key: &rsa::PublicKeyRef
        ) {

        }
        //
        // pub fn vote(&mut self, candidate: &str, cec_public_key: &rsa::PublicKey) -> VoteData {
        //     let gamming_key = rsa::generate_num();
        //
        //     let gammed_vote = gamming_cipher(candidate.as_bytes(), &gamming_key.to_bytes_le());
        //     let gammed_vote_hash = self.key_pair.quad_fold_hash(&gammed_vote);
        //
        //     let rsa_signature = self.key_pair.get_private_key().apply(&gammed_vote_hash).unwrap();
        //     let encrypted_gamming_key = cec_public_key.apply(&gamming_key).unwrap();
        //
        //     VoteData { encrypted_gamming_key, rsa_signature, gammed_vote }
        // }
        //
        // pub fn get_public_key(&self) -> rsa::PublicKey {
        //     self.key_pair.get_public_key()
        // }
    }
}

mod cec {
    use std::collections::HashMap;
    use getset::Getters;
    use num_bigint::BigUint;
    use thiserror::Error;
    use crate::{rsa, voter};
    use crate::voter::{CandidateId, CandidateIdVec, VoterId};

    pub struct CEC {
        candidates: HashMap<String, u64>,
        voters_state: HashMap<VoterId, VoterState>,
        key_pair: rsa::KeyPair,
    }

    #[derive(Error, Debug, PartialEq, Eq)]
    pub enum VoteError {
        #[error("Gamming keys do not match")]
        GammingKeyHashedNotMatch,
        #[error("Failed parse gamming key")]
        FailedParseGammingKey,
        #[error("Failed parse candidate")]
        FailedParseCandidate,
        #[error("Invalid candidate")]
        CandidateNotRegistered,
        #[error("Voter has already voted")]
        VoterAlreadyVoted,
        #[error("Voter can not vote")]
        VoterCanNotVote,
        #[error("Voter is not registered")]
        VoterNotRegistered
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum CanVoteState {
        NotRegistered,
        Registered,
        Voted
    }

    #[derive(Debug, Clone)]
    pub enum VoterState {
        CanVote(CanVoteState),
        CanNotVote,
    }

    #[derive(Error, Debug)]
    pub enum ConsumePacketsError {
        #[error("Failed to deserialize packets_data: {0}")]
        FailedToDeserializePackets(bincode::Error),
        #[error(transparent)]
        FailedCreateUnapplyBlindingOps(#[from] rsa::UnapplyBlindingOpsError),
        #[error("Failed to deserialize candidate_id: {0}")]
        FailedDeserializedCandidateId(bincode::Error),
        #[error(transparent)]
        CheckCandidateIdError(#[from] CheckCandidateIdError),
        #[error("Packet data must have at least two candidate_id_vec")]
        PacketDataTooLittle(usize),
        #[error("Failed to serialize output packet")]
        FailedSerializeOutputCandidateIdVec(bincode::Error)
    }

    #[derive(Error, Debug)]
    enum CheckCandidateIdError {
        #[error("Invalid candidate: {0}")]
        InvalidCandidateError(String),
        #[error("Invalid voter id: {0:?}")]
        InvalidVoterId(VoterId),
        #[error("Invalid voter state: {0:?}")]
        InvalidVoterState(VoterState),
        #[error("Ids are not the same: {0:?} != {1:?}")]
        IdsAreNotTheSame(VoterId, VoterId),
        #[error("Real: {0}, packet: {1}")]
        CandidatesListLenNotMatch(usize, usize)
    }

    fn check_packet<'a>(
        candidate_id_vec_vec: &'a [CandidateIdVec],
        candidates: &'a HashMap<String, u64>,
        voters_state: &'a HashMap<VoterId, VoterState>,
    ) -> Result<VoterId, CheckCandidateIdError> {
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

    impl CEC {
        pub fn new(
            candidates: impl Iterator<Item=String>,
            voters_state: HashMap<VoterId, VoterState>
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
            ciphered_data: &[BigUint]
        ) -> Result<Vec<BigUint>, ConsumePacketsError> {
            let deciphered_data = rsa::decipher_data(
                &self.key_pair.get_private_key_ref(), ciphered_data
            );
            let packet_data: voter::PacketsData = bincode::deserialize(&deciphered_data)
                .map_err(ConsumePacketsError::FailedToDeserializePackets)?;
            if packet_data.get_blinded_candidate_id_vec_vec().is_empty() {
                return Err(ConsumePacketsError::PacketDataTooLittle(
                    packet_data.get_blinded_candidate_id_vec_vec().len()
                ));
            }
            let candidate_id_vec_vec = {
                let unapply_blinding_ops = rsa::UnapplyBlindingOps::new(
                    packet_data.get_blind_key(),
                    self.key_pair.get_product_number()
                )?;
                let mut candidate_id_vec_vec = Vec::<voter::CandidateIdVec>::new();
                for blinded_candidate_id_vec in packet_data
                    .get_blinded_candidate_id_vec_vec().iter().skip(1) {
                    let blinded_candidate_id = unapply_blinding_ops.apply(&blinded_candidate_id_vec.0);
                    candidate_id_vec_vec.push(bincode::deserialize(&blinded_candidate_id)
                        .map_err(ConsumePacketsError::FailedDeserializedCandidateId)?);
                }
                candidate_id_vec_vec
            };
            let voter_id = check_packet(&candidate_id_vec_vec, &self.candidates, &self.voters_state)
                .map_err(Into::<ConsumePacketsError>::into)?;
            let packet = bincode::serialize(packet_data.get_blinded_candidate_id_vec_vec().first().unwrap())
                .map_err(ConsumePacketsError::FailedSerializeOutputCandidateIdVec)?;
            *self.voters_state.get_mut(&voter_id).unwrap() = VoterState::CanVote(CanVoteState::Registered);
            Ok(rsa::cipher_data(&self.key_pair.get_private_key_ref(), &packet))
        }

        // pub fn process_vote(&mut self, voter_key: &rsa::PublicKey, vote_data: voter::VoteData)
        //                     -> Result<(), VoteError> {
        //     if let Some(state) = self.voters_state.get_mut(voter_key) {
        //         match state {
        //             VoterState::Voted => Err(VoteError::VoterAlreadyVoted),
        //             VoterState::CanNotVote => Err(VoteError::VoterCanNotVote),
        //             VoterState::CanVote => {
        //                 let hash = voter_key.quad_fold_hash(vote_data.get_gammed_vote());
        //                 let decrypted_hash = voter_key.apply(vote_data.get_rsa_signature()).unwrap();
        //
        //                 if hash == decrypted_hash {
        //                     if let Some(gamming_key) = self.key_pair.get_private_key()
        //                         .apply(vote_data.get_encrypted_gamming_key()) {
        //                         if let Ok(candidate) = String::from_utf8(
        //                             gamming_cipher(vote_data.get_gammed_vote(), &gamming_key.to_bytes_le())
        //                         ) {
        //                             if let Some(score) = self.candidates.get_mut(candidate.as_str()) {
        //                                 *state = VoterState::Voted;
        //                                 *score += 1;
        //                                 Ok(())
        //                             } else {
        //                                 Err(VoteError::CandidateNotRegistered)
        //                             }
        //                         } else {
        //                             Err(VoteError::FailedParseCandidate)
        //                         }
        //                     } else {
        //                         Err(VoteError::FailedParseGammingKey)
        //                     }
        //                 } else {
        //                     Err(VoteError::GammingKeyHashedNotMatch)
        //                 }
        //             }
        //         }
        //     } else {
        //         Err(VoteError::VoterNotRegistered)
        //     }
        // }

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
    use rand::seq::IteratorRandom;
    use crate::{cec, voter};

    #[test]
    fn test_vote() {
        let mut voters = (0..10).into_iter().map(|_| voter::Voter::new())
            .collect::<Vec<_>>();

        let mut cec = cec::CEC::new(
            (0..10).into_iter().map(|i| format!("Candidate {}", i)),
            HashMap::from_iter(voters.iter().map(|v| (
                v.get_id().clone(), cec::VoterState::CanVote(cec::CanVoteState::NotRegistered)))
            )
        );

        let mut rng = rand::thread_rng();

        for voter in &mut voters {
            let packet = voter.produce_packets(
                NonZeroUsize::new(10).unwrap(), cec.get_candidates().keys(), &cec.get_public_key()
            ).unwrap();
            let signed_candidate_id_vec = cec.consume_packets(&packet).unwrap();

        }

        for el in cec.get_candidates() {
            println!("{:?}", el);
        }
    }

    // #[test]
    // fn test_can_not_vote() {
    //     let mut voter = voter::Voter::new();
    //
    //     let mut cec = cec::CEC::new(
    //         (0..10).into_iter().map(|i| format!("Candidate {}", i)),
    //         HashMap::from([
    //             (voter.get_public_key(), cec::VoterState::CanNotVote)
    //         ])
    //     );
    //
    //     let vote_data = voter.vote(
    //         cec.get_candidates().keys().last().unwrap(),
    //         &cec.get_public_key()
    //     );
    //
    //     let err = cec.process_vote(&voter.get_public_key(), vote_data).unwrap_err();
    //     assert_eq!(err, cec::VoteError::VoterCanNotVote);
    // }
    //
    // #[test]
    // fn test_already_voted() {
    //     let mut voter = voter::Voter::new();
    //
    //     let mut cec = cec::CEC::new(
    //         (0..10).into_iter().map(|i| format!("Candidate {}", i)),
    //         HashMap::from([
    //             (voter.get_public_key(), cec::VoterState::CanVote)
    //         ])
    //     );
    //
    //     let vote_data = voter.vote(
    //         cec.get_candidates().keys().last().unwrap(),
    //         &cec.get_public_key()
    //     );
    //
    //     cec.process_vote(&voter.get_public_key(), vote_data.clone()).unwrap();
    //
    //     let err = cec.process_vote(&voter.get_public_key(), vote_data).unwrap_err();
    //     assert_eq!(err, cec::VoteError::VoterAlreadyVoted);
    // }
}