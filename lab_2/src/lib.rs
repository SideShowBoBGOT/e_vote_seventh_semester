extern crate derive_more;

mod rsa {
    use std::ops::Rem;
    use derive_more::Deref;
    use getset::Getters;
    use lazy_static::lazy_static;
    use num_bigint::{BigUint};
    use num_traits::{One, ToBytes, Zero};
    use rand::Rng;

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

    impl KeyRef for PrivateKeyRef<'_> {
        fn get_parts(&self) -> (&BigUint, &ProductNumber) {
            (self.private_number, self.product_number)
        }
    }

    impl KeyRef for PublicKeyRef<'_> {
        fn get_parts(&self) -> (&BigUint, &ProductNumber) {
            (&PUBLIC_NUMBER, self.product_number)
        }
    }

    fn calc_chunk_size(product_number: &ProductNumber) -> usize {
        let bits = product_number.bits() as usize;
        assert!(bits >= 2);
        bits - 1
    }

    pub struct CipheredData(Vec<BigUint>);
    pub struct DecipheredData(Vec<u8>);

    pub fn cipher_data(key: &impl KeyRef, data: &[u8]) -> CipheredData {
        let (part, product_number) = key.get_parts();
        let chunk_size = calc_chunk_size(product_number);
        CipheredData(
            data.chunks(chunk_size)
                .map(|data_chunk| {
                    BigUint::from_bytes_le(data_chunk).modpow(part, product_number)
                })
                .collect::<Vec<_>>()
        )
    }

    pub fn decipher_data(key: &impl KeyRef, ciphered_data: &CipheredData) -> DecipheredData {
        let (part, product_number) = key.get_parts();
        ciphered_data.0.iter().fold(DecipheredData(Vec::new()), |mut acc, chunk| {
            acc.0.extend(
                chunk.modpow(part, product_number).to_bytes_le()
            );
            acc
        })
    }

    pub struct BlindKey(BigUint);
    impl BlindKey {
        pub fn new(product_number: &ProductNumber) -> Self {
            Self (
                BigUint::one()
                .modinv(product_number)
                .expect("Generation of random multiplicative failed")
            )

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

    pub struct UnapplyBlindingOps {
        mask_multiplicative_inverse: BigUint,
    }

    impl UnapplyBlindingOps {
        pub fn new(blind_key: &BlindKey, product_number: &ProductNumber) -> Self {
            Self {
                mask_multiplicative_inverse: {
                    blind_key.0.modinv(product_number)
                        .expect("Failed to cal modular multiplicative inverse")
                }
            }
        }

        pub fn apply(&self, data: &[BigUint]) -> Vec<u8> {
            data.iter().fold(Vec::new(), |mut acc, chunk| {
                acc.extend((chunk * self.mask_multiplicative_inverse.clone()).to_bytes_le() );
                acc
            })    
        }
    }

    #[cfg(test)]
    mod tests {
        use super::{cipher_data, decipher_data, ApplyBlindingOps, BlindKey, KeyPair, UnapplyBlindingOps};

        #[test]
        fn test_ciphering() {
            let r = KeyPair::new();
            let message = "message";
            let ciphered_data = cipher_data(&r.get_public_key_ref(), message.as_bytes());
            let deciphered_data = decipher_data(&r.get_private_key_ref(), &ciphered_data);
            let deciphered_message = String::from_utf8(deciphered_data.0).unwrap();
            assert_eq!(deciphered_message, message);
            println!("{}", deciphered_message);
        }

        #[test]
        fn test_blinding() {
            let sender = KeyPair::new();
            let receiver = KeyPair::new();
            let message = "message";
            let blind_key = BlindKey::new(sender.get_product_number());
            let apply_blinding_ops = ApplyBlindingOps::new(&blind_key, receiver.get_product_number());
            let unapply_blinding_ops = UnapplyBlindingOps::new(&blind_key, receiver.get_product_number());

            let blinded_data = apply_blinding_ops.apply(message.as_bytes());
            let unblinded_data = unapply_blinding_ops.apply(&blinded_data);
            let unblined_message = String::from_utf8(unblinded_data).unwrap();

            assert_eq!(unblined_message, message);
            println!("{}", unblined_message);
        }

    }
}

mod voter {
    use getset::Getters;
    use num_bigint::BigUint;
    use num_traits::One;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use crate::rsa;
    use crate::rsa::PublicKeyRef;

    #[derive(Getters, Clone)]
    #[getset(get = "pub with_prefix")]
    pub struct VoteData {
        encrypted_gamming_key: BigUint,
        rsa_signature: BigUint,
        gammed_vote: Vec<u8>
    }

    #[derive(Default)]
    pub struct Voter {
        key_pair: rsa::KeyPair,
        id: BigUint
    }

    #[derive(Serialize)]
    struct CandidateIdRef<'a> {
        candidate: &'a str,
        id: &'a BigUint
    }

    struct SerializedCandidateId(Vec<u8>);

    #[derive(Serialize, Deserialize)]
    struct MaskedCandidateId(Vec<BigUint>);

    #[derive(Serialize, Deserialize)]
    struct PacketsData {
        masked_candidate_ids: Vec<MaskedCandidateId>,
        mask_key: BigUint,
    }

    impl Voter {
        pub fn new() -> Self {
            Self {
                key_pair: rsa::KeyPair::new(),
                id: rsa::generate_num()
            }
        }

        pub fn produce_packets<'a>(
            &'a self,
            packets_numer: std::num::NonZeroUsize,
            candidates: impl Iterator<Item=&'a str> + Clone,
            cec_public_key: &PublicKeyRef
        ) {
            let ser_candidate_ids = {
                (0..packets_numer.get())
                    .into_iter()
                    .map(|_| {
                        let candidate_id_pairs = {
                            candidates.clone().map(|c| {
                                CandidateIdRef {candidate: c, id: &self.id }
                            }).collect::<Vec<_>>()
                        };
                        SerializedCandidateId(
                            bincode::serialize(&candidate_id_pairs)
                                .expect("Failed to serialize candidate_id_pairs")
                        )
                    })
                    .collect::<Vec<_>>()
            };
            let mask_key = BigUint::one()
                .modinv(&self.key_pair.get_product_number())
                .expect("Generation of random multiplicative failed");
            let masked_candidate_ids = {
                let chunk_size = {
                    let bits = self.key_pair.get_product_number().bits() as usize;
                    assert!(bits >= 2);
                    bits - 1
                };
                let mask_multiplicative = {
                    mask_key.modpow(&rsa::PUBLIC_NUMBER, cec_public_key.get_product_number())
                };
                ser_candidate_ids.into_iter()
                    .map(|serialized_candidate_id_pair| {
                        MaskedCandidateId(
                            serialized_candidate_id_pair.0.chunks(chunk_size)
                                .map(|data_chunk| {
                                    BigUint::from_bytes_le(data_chunk) * mask_multiplicative.clone()
                                })
                                .collect::<Vec<_>>()
                        )
                    })
                    .collect::<Vec<_>>()
            };
            let packets_data = PacketsData{masked_candidate_ids, mask_key};




            // let masked_serialized = bincode::serialize(&masked)
            //     .expect("Failed to serialize masked packet");


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

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};

    #[test]
    fn test_serialization_1() {
        let n = "message";

        let k = bincode::serialize(n).unwrap();

        let a: String = bincode::deserialize(&k).unwrap();

        println!("{}", a);
    }
    #[test]
    fn test_serialization_2() {
        #[derive(Serialize, Debug)]
        struct SomeRef<'a> {
            massage: &'a str,
            number: &'a usize
        }

        #[derive(Deserialize, Debug)]
        struct SomeValue {
            massage: String,
            number: usize
        }

        let num = 10usize;
        let some_ref = SomeRef { massage: "fdsfdsf", number: &num };
        let serialized = bincode::serialize(&some_ref).unwrap();
        let some_value: SomeValue = bincode::deserialize(&serialized).unwrap();

        println!("{:?}", some_ref);
        println!("{:?}", some_value);
    }
}

// mod cec {
//     use std::collections::HashMap;
//     use thiserror::Error;
//     use crate::rsa;
//     use crate::{gamming_cipher, voter};
//     use crate::rsa::PublicKey;
//
//     pub struct CEC {
//         candidates: HashMap<String, u64>,
//         voters_state: HashMap<rsa::PublicKey, VoterState>,
//         key_pair: rsa::KeyPair,
//     }
//
//     #[derive(Error, Debug, PartialEq, Eq)]
//     pub enum VoteError {
//         #[error("Gamming keys do not match")]
//         GammingKeyHashedNotMatch,
//         #[error("Failed parse gamming key")]
//         FailedParseGammingKey,
//         #[error("Failed parse candidate")]
//         FailedParseCandidate,
//         #[error("Invalid candidate")]
//         CandidateNotRegistered,
//         #[error("Voter has already voted")]
//         VoterAlreadyVoted,
//         #[error("Voter can not vote")]
//         VoterCanNotVote,
//         #[error("Voter is not registered")]
//         VoterNotRegistered
//     }
//
//     #[derive(Debug)]
//     pub enum VoterState {
//         CanVote,
//         CanNotVote,
//         Voted,
//     }
//
//     impl CEC {
//         pub fn new<I>(candidates: I, voters_state: HashMap<rsa::PublicKey, VoterState>) -> Self
//         where I: Iterator<Item=String> {
//             Self {
//                 candidates: HashMap::from_iter(candidates.map(|c| (c, 0u64))),
//                 voters_state,
//                 key_pair: rsa::KeyPair::new()
//             }
//         }
//
//         pub fn process_vote(&mut self, voter_key: &rsa::PublicKey, vote_data: voter::VoteData)
//                             -> Result<(), VoteError> {
//             if let Some(state) = self.voters_state.get_mut(voter_key) {
//                 match state {
//                     VoterState::Voted => Err(VoteError::VoterAlreadyVoted),
//                     VoterState::CanNotVote => Err(VoteError::VoterCanNotVote),
//                     VoterState::CanVote => {
//                         let hash = voter_key.quad_fold_hash(vote_data.get_gammed_vote());
//                         let decrypted_hash = voter_key.apply(vote_data.get_rsa_signature()).unwrap();
//
//                         if hash == decrypted_hash {
//                             if let Some(gamming_key) = self.key_pair.get_private_key()
//                                 .apply(vote_data.get_encrypted_gamming_key()) {
//                                 if let Ok(candidate) = String::from_utf8(
//                                     gamming_cipher(vote_data.get_gammed_vote(), &gamming_key.to_bytes_le())
//                                 ) {
//                                     if let Some(score) = self.candidates.get_mut(candidate.as_str()) {
//                                         *state = VoterState::Voted;
//                                         *score += 1;
//                                         Ok(())
//                                     } else {
//                                         Err(VoteError::CandidateNotRegistered)
//                                     }
//                                 } else {
//                                     Err(VoteError::FailedParseCandidate)
//                                 }
//                             } else {
//                                 Err(VoteError::FailedParseGammingKey)
//                             }
//                         } else {
//                             Err(VoteError::GammingKeyHashedNotMatch)
//                         }
//                     }
//                 }
//             } else {
//                 Err(VoteError::VoterNotRegistered)
//             }
//         }
//
//         pub fn get_candidates(&self) -> &HashMap<String, u64> {
//             &self.candidates
//         }
//
//         pub fn get_public_key(&self) -> PublicKey {
//             self.key_pair.get_public_key()
//         }
//     }
// }

// #[cfg(test)]
// mod tests {
    // use std::collections::HashMap;
    // use rand::seq::IteratorRandom;
    // use super::{gamming_cipher, cec, voter};
    //
    // #[test]
    // fn test_gamming_cypher() {
    //     let message = "spongebob";
    //     let key = "squarepants";
    //
    //     let gammed = gamming_cipher(message.as_bytes(), key.as_bytes());
    //     let ungammed = String::from_utf8(gamming_cipher(&gammed, key.as_bytes())).unwrap();
    //
    //     assert_eq!(ungammed, message);
    // }
    //
    // #[test]
    // fn test_vote() {
    //     let mut voters = (0..100).into_iter().map(|_| voter::Voter::new())
    //         .collect::<Vec<_>>();
    //
    //     let mut cec = cec::CEC::new(
    //         (0..10).into_iter().map(|i| format!("Candidate {}", i)),
    //         HashMap::from_iter(voters.iter().map(|v| (v.get_public_key(), cec::VoterState::CanVote)))
    //     );
    //
    //     let mut rng = rand::thread_rng();
    //
    //     for voter in &mut voters {
    //         let vote_data = voter.vote(
    //             cec.get_candidates().keys().choose(&mut rng).unwrap(),
    //             &cec.get_public_key()
    //         );
    //
    //         if let Err(err) = cec.process_vote(&voter.get_public_key(), vote_data) {
    //             println!("{}", err);
    //         }
    //     }
    //
    //     for el in cec.get_candidates() {
    //         println!("{:?}", el);
    //     }
    // }
    //
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
// }