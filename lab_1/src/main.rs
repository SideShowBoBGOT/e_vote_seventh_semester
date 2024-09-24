use std::marker::PhantomData;
use rand::Rng;
use rand::seq::IteratorRandom;
use crate::voter::{GammingKeyType, VoterState};
use num_traits::One;

mod rsa {
    use std::ops::Rem;
    use lazy_static::lazy_static;
    use num_bigint::{BigInt, BigUint, RandBigInt, ToBigInt};
    use num_traits::{CheckedEuclid, Euclid, One, Zero};
    use rand::Rng;
    pub use keys::{KeyPair, PublicKey, PrivateKey, MIN_N};

    const MIN_GENERATED_NUMBER: u32 = u16::MAX as u32;
    const MAX_GENERATED_NUMBER: u32 = u32::MAX;

    fn generate_num(predicate: fn(&BigUint) -> bool) -> BigUint {
        let mut rng = rand::thread_rng();
        loop {
            let num = BigUint::from(rng.gen_range(MIN_GENERATED_NUMBER..MAX_GENERATED_NUMBER));
            if predicate(&num) {
                return num;
            }
        }
    }

    lazy_static! {
        static ref TWO: BigUint = BigUint::from(2u32);
    }

    fn is_uneven(num: &BigUint) -> bool {
        num.bit(0)
    }

    #[cfg(test)]
    mod tests {
        use num_bigint::BigUint;
        use crate::rsa::is_uneven;

        #[test]
        fn test_is_uneven() {
            for i in 0..100000u32 {
                assert_eq!(is_uneven(&BigUint::from(i)), i % 2 == 1);
            }
        }
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
        generate_num(is_prime)
    }

    fn generate_uneven() -> BigUint {
        generate_num(is_uneven)
    }

    fn extended_gcd(a: BigUint, b: BigUint) -> (BigUint, BigInt, BigInt) {
        if a.is_zero() {
            return (b, BigInt::zero(), BigInt::one());
        }

        let (gcd, x1, y1) = extended_gcd(b.clone() % a.clone(), a.clone());
        let x = y1 - (b / a).to_bigint().unwrap() * x1.clone();
        let y = x1;

        (gcd, x, y)
    }

    mod keys {
        use lazy_static::lazy_static;
        use num_bigint::BigUint;
        use num_traits::{One, Zero};
        use crate::rsa::{generate_prime, generate_uneven, MIN_GENERATED_NUMBER, TWO};

        fn quad_fold_hash(n: &BigUint, data: &[u8]) -> BigUint {
            data.iter().fold(BigUint::zero(), |acc, x| {
                (acc + BigUint::from(*x)).modpow(&TWO, &n)
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

            pub fn quad_fold_hash(&self, data: &[u8]) -> BigUint {
                quad_fold_hash(&self.n, data)
            }
        }

        pub struct PublicKey {
            e: BigUint,
            n: BigUint
        }

        impl PublicKey {
            pub fn apply(&self, data: &BigUint) -> Option<BigUint> {
                apply_key(data, &self.e, &self.n)
            }

            pub fn quad_fold_hash(&self, data: &[u8]) -> BigUint {
                quad_fold_hash(&self.n, data)
            }
        }

        #[derive(Debug, Clone)]
        pub struct KeyPair {
            n: BigUint,
            e: BigUint,
            d: BigUint,
        }

        impl Default for KeyPair {
            fn default() -> Self {
                Self {
                    n: BigUint::from(9u32),
                    e: BigUint::from(3u32),
                    d: BigUint::from(3u32)
                }
            }
        }

        lazy_static! {
            pub static ref MIN_N: BigUint = BigUint::from(MIN_GENERATED_NUMBER).pow(2);
        }

        impl KeyPair {
            pub fn new() -> Self {
                loop {
                    let p = generate_prime();
                    let q = generate_prime();
                    let n = p.clone() * q.clone();
                    let phi = (p.clone() - BigUint::one()) * (q.clone() - BigUint::one());
                    let e = generate_uneven();
                    if e < phi {
                        if let Some(d) = e.clone().modinv(&phi) {
                            return Self { n, e, d }
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
                PublicKey { n: self.n.clone(), e: self.e.clone() }
            }
        }
        #[cfg(test)]
        mod tests {
            use num_bigint::BigUint;
            use super::{quad_fold_hash, KeyPair};

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
    use rand::Rng;
    use static_assertions::const_assert;
    use crate::{gamming_cipher, rsa};
    use crate::rsa::PublicKey;

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

    pub type GammingKeyType = u16;

    impl VoterState {
        pub fn vote(&mut self, candidate: &str, cec_public_key: rsa::PublicKey) -> Result<VoteData, VoteError> {
            match self {
                VoterState::CanVote(voter) => {
                    let mut rng = rand::thread_rng();
                    let mut gamming_key = GammingKeyType::MIN.to_le_bytes();
                    for e in &mut gamming_key {
                        *e = rng.gen_range(0..u8::MAX)
                    }

                    let gammed_vote = gamming_cipher(candidate.as_bytes(), &gamming_key);
                    let gammed_vote_hash = voter.key_pair.quad_fold_hash(&gammed_vote);

                    let rsa_signature = voter.key_pair.get_private_key().apply(&gammed_vote_hash).unwrap();
                    let gamming_key = BigUint::from(GammingKeyType::from_le_bytes(gamming_key));
                    let encrypted_gamming_key = cec_public_key.apply(&gamming_key).unwrap();

                    *self = VoterState::Voted(std::mem::take(voter));
                    Ok(VoteData { encrypted_gamming_key, rsa_signature, gammed_vote })
                },
                VoterState::CanNotVote(_) => Err(VoteError::CanNotVote),
                VoterState::Voted(_) => Err(VoteError::AlreadyVoted),
            }
        }

        pub fn get_public_key(&self) -> PublicKey {
            match self {
                VoterState::CanVote(voter) => voter.key_pair.get_public_key(),
                VoterState::CanNotVote(voter) => voter.key_pair.get_public_key(),
                VoterState::Voted(voter) => voter.key_pair.get_public_key(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use num_bigint::BigUint;
    use num_traits::ToPrimitive;
    use rand::seq::IteratorRandom;
    use static_assertions::const_assert;
    use crate::voter::{GammingKeyType, VoterData};
    use super::{gamming_cipher, rsa, VoterState};

    #[test]
    fn test_assertions() {
        assert!(BigUint::from(GammingKeyType::MAX) < *rsa::MIN_N);
    }

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
        let mut voters = (0..10).into_iter()
            .map(|_| VoterState::CanVote(VoterData::new())).collect::<Vec<_>>();
        let key_pair = rsa::KeyPair::new();
        let mut vote_cand = HashMap::<String, u64>::from_iter(
            (0..5).into_iter().map(|i| (format!("Candidate {}", i), 0u64))
        );

        for voter in &mut voters {
            let vote_data = voter.vote(
                vote_cand.keys().choose(&mut rand::thread_rng()).unwrap(),
                key_pair.get_public_key()
            ).unwrap();

            let hash = voter.get_public_key().quad_fold_hash(vote_data.get_gammed_vote());
            let decrypted_hash = voter.get_public_key().apply(vote_data.get_rsa_signature()).unwrap();

            if hash != decrypted_hash {
                println!("Hashes do not match");
                continue;
            }

            if let Some(decrypted_gamming_key) = key_pair.get_private_key()
                .apply(vote_data.get_encrypted_gamming_key()) {

                if let Some(gamming_key) = decrypted_gamming_key.to_u16() {

                    let gamming_key_arr = gamming_key.to_le_bytes();
                    if let Ok(candidate) = String::from_utf8(gamming_cipher(vote_data.get_gammed_vote(), &gamming_key_arr)) {
                        if let Some(score) = vote_cand.get_mut(&candidate) {
                            *score += 1;
                        } else {
                            println!("Invalid candidate");
                            continue;
                        }
                    } else {
                        println!("Can not parse candidate");
                        continue;
                    }
                } else {
                    println!("Decrypted gamming key is too large");
                }
            } else {
                println!("Can not parse gamming key");
            }
        }
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