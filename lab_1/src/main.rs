use rand::Rng;
use std::collections::HashMap;
use thiserror::Error;
use crate::rsa::RSA;

mod rsa {
    use rand::Rng;
    pub use inner::RSA;

    fn generate_num(predicate: fn(u16) -> bool) -> u16 {
        let mut rng = rand::thread_rng();
        loop {
            let num = rng.gen_range(0..u16::MAX);
            if predicate(num) {
                return num;
            }
        }
    }

    fn is_uneven(num: u16) -> bool {
        num % 2 == 1
    }

    fn is_prime(n: u16) -> bool {
        if n < 2 {
            return false;
        }
        for i in 2..=(n as f64).sqrt() as u16 {
            if n % i == 0 {
                return false;
            }
        }
        true
    }

    fn generate_prime() -> u16 {
        generate_num(is_prime)
    }

    fn generate_uneven() -> u16 {
        generate_num(is_uneven)
    }

    fn extended_gcd(a: u32, b: u32) -> (u32, i64, i64) {
        if a == 0 {
            return (b, 0, 1);
        }

        let (gcd, x1, y1) = extended_gcd(b % a, a);
        let x = y1 - ((b / a) as i64) * x1;
        let y = x1;

        (gcd, x, y)
    }

    fn calc_multiplier_mod_1(e: u32, phi: u32) -> Option<u32> {
        let (g, x, _) = extended_gcd(e, phi);
        if g != 1 {
            return None;
        }
        let phi = phi as i64;
        Some(((x % phi + phi) % phi) as u32)
    }

    fn mod_pow(base: u64, exponent: u64, modulus: u64) -> u64 {
        let mut result = 1;
        let mut base = base % modulus;
        let mut exp = exponent;
        while exp > 0 {
            if exp % 2 == 1 {
                result = (result * base) % modulus;
            }
            exp = exp >> 1;
            base = (base * base) % modulus;
        }
        result
    }

    mod inner {
        use crate::rsa::{generate_prime, generate_uneven, calc_multiplier_mod_1, mod_pow};

        #[derive(Debug, Copy, Clone)]
        pub struct MessageHash(u32);

        #[derive(Debug, Copy, Clone)]
        pub struct Signature(u64);

        #[derive(Debug, Clone)]
        pub struct RSA {
            n: u32,
            e: u16,
            d: u32,
        }

        impl RSA {
            pub fn new() -> Self {
                loop {
                    let p = generate_prime() as u32;
                    let q = generate_prime() as u32;
                    let n = p * q;
                    let phi = (p - 1) * (q - 1);
                    let e = generate_uneven();
                    if (e as u32) < phi {
                        if let Some(d) = calc_multiplier_mod_1(e as u32, phi) {
                            return Self { n, e, d }
                        }
                    }
                }
            }

            pub fn hash(&self, msg: &str) -> MessageHash {
                MessageHash(msg.chars().fold(0u32, |acc, x| (acc + x as u32).pow(2) % self.n))
            }

            pub fn sign(&self, hash: MessageHash) -> Signature {
                Signature(mod_pow(hash.0 as u64, self.d as u64, self.n as u64))
            }

            pub fn verify_signature(&self, signature: Signature) -> bool {
                mod_pow(signature.0, self.e as u64, self.n as u64) == signature.0
            }
        }

        #[cfg(test)]
        mod tests {
            use crate::rsa::RSA;

            #[test]
            fn test_rsa() {
                let r = RSA::new();
                println!("{:?}", r);
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::rsa::{calc_multiplier_mod_1, mod_pow};

        #[test]


        #[test]
        fn test_mod_inverse() {
            assert_eq!(calc_multiplier_mod_1(7, 10), Some(3));
            assert_eq!(calc_multiplier_mod_1(3, 5), Some(2));
            assert_eq!(calc_multiplier_mod_1(13, 25), Some(2));
            assert_eq!(calc_multiplier_mod_1(10, 11), Some(10));
        }

        #[test]
        fn test_mod_pow() {
            assert_eq!(mod_pow(2, 6, 53), 11);
            assert_eq!(mod_pow(3, 4, 64), 17);
            assert_eq!(mod_pow(5, 4, 100), 25);
            assert_eq!(mod_pow(11, 2, 13), 4);
        }
    }
}

fn gamming_cipher(message: &str, key: &str) -> String {
    message
        .chars()
        .zip(key.chars().cycle())
        .map(|(m, k)| (m as u8 ^ k as u8) as char)
        .collect()
}

// struct VoterData {
//     name: String,
//     rsa: RSA
// }
//
// enum VoterState {
//     CanVote(VoterData),
//     CanNotVote(VoterData),
//     Voted(VoterData),
// }
//
// #[derive(Error, Debug)]
// enum VoteError {
//     CanNotVote,
//     AlreadyVoted,
// }
//
// impl VoterState {
//     fn vote(self) -> (VoterState, Result<(), VoteError>) {
//         match self {
//             VoterState::CanVote(voter) => (VoterState::Voted(voter), Ok(())),
//             voter @ VoterState::CanNotVote(_) => (voter, Err(VoteError::CanNotVote)),
//             voter @ VoterState::CanNotVote(_) => (voter, Err(VoteError::AlreadyVoted)),
//         }
//     }
// }
//
// impl Voter {
//     fn new(name: &str, has_right_to_vote: bool) -> Self {
//         Voter {
//             name: name.to_string(),
//             has_right_to_vote,
//             has_voted: false,
//             rsa: RSA::new(),
//         }
//     }
//
//     fn vote(&mut self, candidate: &str, cec_public_key: (u64, u64)) -> Option<(String, u64, u64)> {
//         if !self.has_right_to_vote {
//             println!("{}: Виборець не має права голосувати", self.name);
//             return None;
//         }
//         if self.has_voted {
//             println!("{}: Виборець вже проголосував", self.name);
//             return None;
//         }
//
//         let mut rng = rand::thread_rng();
//         let key: String = (0..16).map(|_| rng.gen_range(0..16).to_string()).collect();
//         let encrypted_vote = gamming_cipher(candidate, &key);
//         let signature = self.rsa.sign(encrypted_vote.as_bytes().iter().fold(0, |acc, &x| (acc << 8) | x as u64));
//         let encrypted_key = mod_pow(key.as_bytes().iter().fold(0, |acc, &x| (acc << 8) | x as u64), cec_public_key.0, cec_public_key.1);
//
//         self.has_voted = true;
//         Some((encrypted_vote, encrypted_key, signature))
//     }
// }
//
// struct CEC {
//     candidates: Vec<String>,
//     voters: HashMap<String, Voter>,
//     votes: Vec<String>,
//     rsa: RSA,
// }
//
// impl CEC {
//     fn new(candidates: Vec<String>, voters: Vec<Voter>) -> Self {
//         let voters_map = voters.into_iter().map(|v| (v.name.clone(), v)).collect();
//         CEC {
//             candidates,
//             voters: voters_map,
//             votes: Vec::new(),
//             rsa: RSA::new(),
//         }
//     }
//
//     fn receive_vote(&mut self, voter_name: &str, vote_data: (String, u64, u64)) -> String {
//         let voter = match self.voters.get_mut(voter_name) {
//             Some(v) => v,
//             None => return "Виборець не зареєстрований".to_string(),
//         };
//
//         if !voter.has_right_to_vote {
//             return "Виборець не має права голосувати".to_string();
//         }
//         if voter.has_voted {
//             return "Виборець вже проголосував".to_string();
//         }
//
//         let (encrypted_vote, encrypted_key, signature) = vote_data;
//
//         if !voter.rsa.verify(encrypted_vote.as_bytes().iter().fold(0, |acc, &x| (acc << 8) | x as u64), signature) {
//             return "Недійсний підпис".to_string();
//         }
//
//         let key = self.rsa.decrypt(encrypted_key).to_string();
//         let vote = gamming_cipher(&encrypted_vote, &key);
//
//         if !self.candidates.contains(&vote) {
//             return "Недійсний голос".to_string();
//         }
//
//         self.votes.push(vote);
//         voter.has_voted = true;
//         "Голос прийнятий".to_string()
//     }
//
//     fn count_votes(&self) -> HashMap<String, usize> {
//         let mut results = HashMap::new();
//         for candidate in &self.candidates {
//             results.insert(candidate.clone(), self.votes.iter().filter(|&v| v == candidate).count());
//         }
//         results
//     }
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