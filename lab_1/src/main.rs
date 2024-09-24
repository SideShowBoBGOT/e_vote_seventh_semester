mod rsa {
    use std::ops::Rem;
    use lazy_static::lazy_static;
    use num_bigint::{BigUint};
    use num_traits::{One, Zero};
    use rand::Rng;
    pub use keys::{KeyPair, PublicKey};

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

    mod keys {
        use lazy_static::lazy_static;
        use num_bigint::BigUint;
        use num_traits::{One, Zero};
        use crate::rsa::{generate_prime, TWO};

        lazy_static! {
            pub static ref E_PRIME: BigUint = BigUint::from(65537u32);
        }

        fn quad_fold_hash(n: &BigUint, data: &[u8]) -> BigUint {
            data.iter().fold(BigUint::zero(), |acc, x| {
                (acc + BigUint::from(*x)).modpow(&TWO, n)
            })
        }

        fn apply_key(data: &BigUint, exp: &BigUint, modulus: &BigUint) -> Option<BigUint> {
            if data > modulus {
                return None;
            }
            Some(data.modpow(exp, modulus))
        }

        pub struct PrivateKey {
            d: BigUint,
            n: BigUint
        }

        impl PrivateKey {
            pub fn apply(&self, data: &BigUint) -> Option<BigUint> {
                apply_key(data, &self.d, &self.n)
            }
        }

        #[derive(Debug, Hash, PartialEq, Eq)]
        pub struct PublicKey {
            n: BigUint
        }

        impl PublicKey {
            pub fn apply(&self, data: &BigUint) -> Option<BigUint> {
                apply_key(data, &E_PRIME, &self.n)
            }

            pub fn quad_fold_hash(&self, data: &[u8]) -> BigUint {
                quad_fold_hash(&self.n, data)
            }
        }

        #[derive(Debug, Clone)]
        pub struct KeyPair {
            n: BigUint,
            d: BigUint,
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
                    let n = p.clone() * q.clone();
                    let phi = (p.clone() - BigUint::one()) * (q.clone() - BigUint::one());
                    if *E_PRIME < phi {
                        if let Some(d) = E_PRIME.modinv(&phi) {
                            return Self { n, d }
                        }
                    }
                }
            }

            pub fn quad_fold_hash(&self, data: &[u8]) -> BigUint {
                quad_fold_hash(&self.n, data)
            }

            pub fn get_private_key(&self) -> PrivateKey {
                PrivateKey { n: self.n.clone(), d: self.d.clone() }
            }

            pub fn get_public_key(&self) -> PublicKey {
                PublicKey { n: self.n.clone() }
            }
        }
        #[cfg(test)]
        mod tests {
            use super::{KeyPair};

            #[test]
            fn test_sign_verify() {
                let r = KeyPair::new();
                let message_hash = r.quad_fold_hash("message".as_bytes());

                let encrypted_hash = r.get_private_key().apply(&message_hash).unwrap();
                assert_eq!(r.get_public_key().apply(&encrypted_hash).unwrap(), message_hash);

                let encrypted_hash = r.get_public_key().apply(&message_hash).unwrap();
                assert_eq!(r.get_private_key().apply(&encrypted_hash).unwrap(), message_hash);
            }
        }
    }
}

fn gamming_cipher(message: &[u8], key: &[u8]) -> Vec<u8> {
    message.iter().zip(key.iter().cycle()).map(|(m, k)| m ^ k).collect()
}

mod voter {
    use getset::Getters;
    use num_bigint::BigUint;
    use crate::{gamming_cipher, rsa};

    #[derive(Default)]
    pub struct VoterData { key_pair: rsa::KeyPair }
    impl VoterData {
        pub fn new() -> Self {
            Self { key_pair: rsa::KeyPair::new() }
        }
    }

    pub enum VoterState {
        CanVote(VoterData),
        CanNotVote(VoterData),
        Voted(VoterData),
    }

    #[derive(Debug)]
    pub enum VoteError {
        CanNotVote,
        AlreadyVoted,
    }

    #[derive(Getters)]
    #[getset(get = "pub with_prefix")]
    pub struct VoteData {
        encrypted_gamming_key: BigUint,
        rsa_signature: BigUint,
        gammed_vote: Vec<u8>
    }

    impl VoterState {
        pub fn vote(&mut self, candidate: &str, cec_public_key: rsa::PublicKey) -> Result<VoteData, VoteError> {
            match self {
                VoterState::CanVote(voter) => {
                    let gamming_key = rsa::generate_num();

                    let gammed_vote = gamming_cipher(candidate.as_bytes(), &gamming_key.to_bytes_le());
                    let gammed_vote_hash = voter.key_pair.quad_fold_hash(&gammed_vote);

                    let rsa_signature = voter.key_pair.get_private_key().apply(&gammed_vote_hash).unwrap();
                    let encrypted_gamming_key = cec_public_key.apply(&gamming_key).unwrap();

                    *self = VoterState::Voted(std::mem::take(voter));
                    Ok(VoteData { encrypted_gamming_key, rsa_signature, gammed_vote })
                },
                VoterState::CanNotVote(_) => Err(VoteError::CanNotVote),
                VoterState::Voted(_) => Err(VoteError::AlreadyVoted),
            }
        }

        pub fn get_public_key(&self) -> rsa::PublicKey {
            match self {
                VoterState::CanVote(voter) => voter.key_pair.get_public_key(),
                VoterState::CanNotVote(voter) => voter.key_pair.get_public_key(),
                VoterState::Voted(voter) => voter.key_pair.get_public_key(),
            }
        }
    }
}

mod cec {
    use std::collections::HashMap;
    use rand::seq::IteratorRandom;
    use thiserror::Error;
    use crate::rsa;
    use crate::{gamming_cipher, voter};

    pub struct CEC {
        candidates: HashMap<&'static str, u64>,
        voters_state: HashMap<rsa::PublicKey, VoterState>,
        key_pair: rsa::KeyPair,
    }

    #[derive(Error, Debug)]
    pub enum VoteError {
        #[error("Gamming keys do not match")]
        GammingKeyHashedNotMatch,
        #[error("Failed parse gamming key")]
        FailedParseGammingKey,
        #[error("Failed parse candidate")]
        FailedParseCandidate,
        #[error("Invalid candidate")]
        InvalidCandidate,
        #[error("Voter has already voted")]
        VoterAlreadyVoted,
        #[error("Voter can not vote")]
        VoterCanNotVote,
        #[error("Voter is not registered")]
        VoterNotRegistered
    }

    pub enum VoterState {
        CanVote,
        CanNotVote,
        Voted,
    }

    impl CEC {
        pub fn new<I>(candidates: I, voters_state: HashMap<rsa::PublicKey, VoterState>) -> Self
            where I: Iterator<Item=&str> {
            Self {
                candidates: HashMap::from(candidates.map(|c| (c, 0u64))),
                voters_state,
                key_pair: rsa::KeyPair::new()
            }
        }

        fn process_vote(&mut self, voter_key: &rsa::PublicKey, vote_data: voter::VoteData)
            -> Result<(), VoteError> {
            if let Some(state) = self.voters_state.get(voter_key) {
                match state {
                    VoterState::Voted => Err(VoteError::VoterAlreadyVoted),
                    VoterState::CanNotVote => Err(VoteError::VoterCanNotVote),
                    VoterState::CanVote => {
                        let hash = voter_key.quad_fold_hash(vote_data.get_gammed_vote());
                        let decrypted_hash = voter_key.apply(vote_data.get_rsa_signature()).unwrap();
                        if hash == decrypted_hash {
                            if let Some(gamming_key) = self.key_pair.get_private_key()
                                .apply(vote_data.get_encrypted_gamming_key()) {
                                if let Ok(candidate) = String::from_utf8(
                                    gamming_cipher(vote_data.get_gammed_vote(), &gamming_key.to_bytes_le())
                                ) {
                                    if let Some(score) = self.candidates.get_mut(&candidate) {
                                        *score += 1;
                                        Ok(())
                                    } else {
                                        Err(VoteError::InvalidCandidate)
                                    }
                                } else {
                                    Err(VoteError::InvalidCandidate)
                                }
                            } else {
                                Err(VoteError::FailedParseGammingKey)
                            }
                        } else {
                            Err(VoteError::GammingKeyHashedNotMatch)
                        }
                    }
                }
            } else {
                Err(VoteError::VoterNotRegistered)
            }
        }

        fn do_organize_vote(
            voters: &mut [voter::VoterState],
            candidates: &mut HashMap<String, u64>,
            key_pair: &rsa::KeyPair
        ) -> Result<(), VoteError> {
            for voter in voters {

                let vote_data = voter.vote(
                    candidates.keys().choose(&mut rand::thread_rng()).unwrap(),
                    key_pair.get_public_key()
                ).unwrap();



            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use crate::cec::CEC;
    use crate::voter::{VoterData};
    use super::{gamming_cipher, voter};

    #[test]
    fn test_gamming_cypher() {
        let message = "spongebob";
        let key = "squarepants";

        let gammed = gamming_cipher(message.as_bytes(), key.as_bytes());
        let ungammed = String::from_utf8(gamming_cipher(&gammed, key.as_bytes())).unwrap();

        assert_eq!(ungammed, message);
    }

    #[test]
    fn test_vote() {
        let voters = (0..100).into_iter()
            .map(|_| voter::VoterState::CanVote(VoterData::new())).collect::<Vec<_>>();
        let vote_cand = HashMap::<String, u64>::from_iter(
            (0..5).into_iter().map(|i| (format!("Candidate {}", i), 0u64))
        );
        let mut cec = CEC::new(voters, vote_cand);
        cec.organize_vote().unwrap();

        cec.
    }
}



    // fn count_votes(&self) -> HashMap<String, usize> {
    //     let mut results = HashMap::new();
    //     for candidate in &self.candidates {
    //         results.insert(candidate.clone(), self.votes.iter().filter(|&v| v == candidate).count());
    //     }
    //     results
    // }

fn main() {
    // let candidates = vec!["Кандидат A".to_string(), "Кандидат B".to_string(), "Кандидат C".to_string()];
    // let voters = vec![
    //     Voter::new("Виборець 1", true),
    //     Voter::new("Виборець 2", true),
    //     Voter::new("Виборець 3", true),
    //     Voter::new("Виборець 4", true),
    //     Voter::new("Виборець 5", false),
    // ];
    //
    // let mut cec = CEC::new(candidates.clone(), voters);
    //
    // let mut rng = rand::thread_rng();
    // for voter_name in ["Виборець 1", "Виборець 2", "Виборець 3", "Виборець 4", "Виборець 5"] {
    //     if let Some(voter) = cec.voters.get_mut(voter_name) {
    //         let candidate = candidates[rng.gen_range(0..candidates.len())].clone();
    //         if let Some(vote_data) = voter.vote(&candidate, (cec.rsa.e, cec.rsa.n)) {
    //             let result = cec.receive_vote(voter_name, vote_data);
    //             println!("{}: {}", voter_name, result);
    //         }
    //     }
    // }
    //
    // // Спроба повторного голосування
    // if let Some(voter) = cec.voters.get_mut("Виборець 1") {
    //     let candidate = candidates[rng.gen_range(0..candidates.len())].clone();
    //     if let Some(_) = voter.vote(&candidate, (cec.rsa.e, cec.rsa.n)) {
    //         println!("Спроба повторного голосування Виборець 1: Виборець вже проголосував");
    //     }
    // }
    //
    // // Підрахунок голосів
    // let results = cec.count_votes();
    // println!("\nРезультати голосування:");
    // for (candidate, votes) in results {
    //     println!("{}: {} голосів", candidate, votes);
    // }
}