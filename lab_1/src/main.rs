use rand::Rng;
use std::collections::HashMap;
use thiserror::Error;
use crate::rsa::RSA;

mod rsa {
    use std::ops::Mul;
    use rand::Rng;
    pub use inner::RSA;

    fn is_prime(n: u32) -> bool {
        if n < 2 {
            return false;
        }
        for i in 2..=(n as f64).sqrt() as u32 {
            if n % i == 0 {
                return false;
            }
        }
        true
    }

    mod big_nums {
        use std::ops::Mul;
        use rand::Rng;
        use super::is_prime;

        // Number between 2^31..(2^32 - 1)
        pub struct BigU32(u32);

        // Number between (2^31 - 1)..((2^32 - 1) - 1)
        pub struct BigDecU32(u32);

        impl Mul for BigU32 {
            type Output = BigU64;

            fn mul(self, rhs: Self) -> Self::Output {
                self.0 * rhs.0
            }
        }

        impl BigU32 {
            pub fn dec(self) -> BigDecU32 {
                BigDecU32(self.0 - 1)
            }

            pub fn value(self) -> u32 {
                self.0
            }
        }

        pub struct BigU64(u64);

        impl BigU64 {
            pub fn value(self) -> u64 {
                self.0
            }
        }

        pub fn generate_big_prime() -> BigU32 {
            let mut rng = rand::thread_rng();
            const MIN_LIMIT: u32 = 1 << 31;
            const MAX_LIMIT: u32 = 1 << 32 - 1;
            loop {
                let num: u32 = rng.gen_range(MIN_LIMIT..MAX_LIMIT);
                if is_prime(num) {
                    return BigU32(num);
                }
            }
        }
    }





    fn extended_gcd(a: u64, b: u64) -> (u64, u64, u64) {
        if a == 0 {
            return (b, 0, 1);
        }

        let (gcd, x1, y1) = extended_gcd(b % a, a);
        let x = y1 - (b / a) * x1;
        let y = x1;

        (gcd, x, y)
    }

    fn mod_inverse(e: u64, phi: u64) -> Option<u64> {
        let (g, x, _) = extended_gcd(e, phi);
        if g != 1 {
            return None;
        }
        Some((x % phi + phi) % phi)
    }

    mod inner {
        use crate::rsa::{generate_big_prime, mod_inverse};

        #[derive(Debug, Copy, Clone)]
        pub struct MessageHash(u64);

        pub struct RSA {
            n: u64,
            e: u64,
            d: u64,
        }

        impl RSA {
            pub fn new() -> Self {
                loop {
                    let (e, n, phi) = loop {
                        let p = generate_big_prime();
                        let q = generate_big_prime();
                        let n = p * q;
                        let phi = (p - 1) * (q - 1);
                        let e = generate_big_prime();
                        if (e as u64) < phi {
                            break (e, n, phi)
                        }
                    };
                    if let Some(d) = mod_inverse(e, phi) {
                        break Self { n, e, d }
                    }
                }
            }

            pub fn hash(&self, msg: &str) -> MessageHash {
                MessageHash(msg.chars().fold(0u64, |acc, x| (acc + x as u64).pow(2) % self.n))
            }

            pub fn sign(&self, hash: MessageHash) -> u64 {
                hash.0.pow(self.d) % self.n
            }
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

struct VoterData {
    name: String,
    rsa: RSA
}

enum VoterState {
    CanVote(VoterData),
    CanNotVote(VoterData),
    Voted(VoterData),
}

#[derive(Error, Debug)]
enum VoteError {
    CanNotVote,
    AlreadyVoted,
}

impl VoterState {
    fn vote(self) -> (VoterState, Result<(), VoteError>) {
        match self {
            VoterState::CanVote(voter) => (VoterState::Voted(voter), Ok(())),
            voter @ VoterState::CanNotVote(_) => (voter, Err(VoteError::CanNotVote)),
            voter @ VoterState::CanNotVote(_) => (voter, Err(VoteError::AlreadyVoted)),
        }
    }
}

impl Voter {
    fn new(name: &str, has_right_to_vote: bool) -> Self {
        Voter {
            name: name.to_string(),
            has_right_to_vote,
            has_voted: false,
            rsa: RSA::new(),
        }
    }

    fn vote(&mut self, candidate: &str, cec_public_key: (u64, u64)) -> Option<(String, u64, u64)> {
        if !self.has_right_to_vote {
            println!("{}: Виборець не має права голосувати", self.name);
            return None;
        }
        if self.has_voted {
            println!("{}: Виборець вже проголосував", self.name);
            return None;
        }

        let mut rng = rand::thread_rng();
        let key: String = (0..16).map(|_| rng.gen_range(0..16).to_string()).collect();
        let encrypted_vote = gamming_cipher(candidate, &key);
        let signature = self.rsa.sign(encrypted_vote.as_bytes().iter().fold(0, |acc, &x| (acc << 8) | x as u64));
        let encrypted_key = mod_pow(key.as_bytes().iter().fold(0, |acc, &x| (acc << 8) | x as u64), cec_public_key.0, cec_public_key.1);

        self.has_voted = true;
        Some((encrypted_vote, encrypted_key, signature))
    }
}

struct CEC {
    candidates: Vec<String>,
    voters: HashMap<String, Voter>,
    votes: Vec<String>,
    rsa: RSA,
}

impl CEC {
    fn new(candidates: Vec<String>, voters: Vec<Voter>) -> Self {
        let voters_map = voters.into_iter().map(|v| (v.name.clone(), v)).collect();
        CEC {
            candidates,
            voters: voters_map,
            votes: Vec::new(),
            rsa: RSA::new(),
        }
    }

    fn receive_vote(&mut self, voter_name: &str, vote_data: (String, u64, u64)) -> String {
        let voter = match self.voters.get_mut(voter_name) {
            Some(v) => v,
            None => return "Виборець не зареєстрований".to_string(),
        };

        if !voter.has_right_to_vote {
            return "Виборець не має права голосувати".to_string();
        }
        if voter.has_voted {
            return "Виборець вже проголосував".to_string();
        }

        let (encrypted_vote, encrypted_key, signature) = vote_data;

        if !voter.rsa.verify(encrypted_vote.as_bytes().iter().fold(0, |acc, &x| (acc << 8) | x as u64), signature) {
            return "Недійсний підпис".to_string();
        }

        let key = self.rsa.decrypt(encrypted_key).to_string();
        let vote = gamming_cipher(&encrypted_vote, &key);

        if !self.candidates.contains(&vote) {
            return "Недійсний голос".to_string();
        }

        self.votes.push(vote);
        voter.has_voted = true;
        "Голос прийнятий".to_string()
    }

    fn count_votes(&self) -> HashMap<String, usize> {
        let mut results = HashMap::new();
        for candidate in &self.candidates {
            results.insert(candidate.clone(), self.votes.iter().filter(|&v| v == candidate).count());
        }
        results
    }
}

fn main() {
    let candidates = vec!["Кандидат A".to_string(), "Кандидат B".to_string(), "Кандидат C".to_string()];
    let voters = vec![
        Voter::new("Виборець 1", true),
        Voter::new("Виборець 2", true),
        Voter::new("Виборець 3", true),
        Voter::new("Виборець 4", true),
        Voter::new("Виборець 5", false),
    ];

    let mut cec = CEC::new(candidates.clone(), voters);

    let mut rng = rand::thread_rng();
    for voter_name in ["Виборець 1", "Виборець 2", "Виборець 3", "Виборець 4", "Виборець 5"] {
        if let Some(voter) = cec.voters.get_mut(voter_name) {
            let candidate = candidates[rng.gen_range(0..candidates.len())].clone();
            if let Some(vote_data) = voter.vote(&candidate, (cec.rsa.e, cec.rsa.n)) {
                let result = cec.receive_vote(voter_name, vote_data);
                println!("{}: {}", voter_name, result);
            }
        }
    }

    // Спроба повторного голосування
    if let Some(voter) = cec.voters.get_mut("Виборець 1") {
        let candidate = candidates[rng.gen_range(0..candidates.len())].clone();
        if let Some(_) = voter.vote(&candidate, (cec.rsa.e, cec.rsa.n)) {
            println!("Спроба повторного голосування Виборець 1: Виборець вже проголосував");
        }
    }

    // Підрахунок голосів
    let results = cec.count_votes();
    println!("\nРезультати голосування:");
    for (candidate, votes) in results {
        println!("{}: {} голосів", candidate, votes);
    }
}