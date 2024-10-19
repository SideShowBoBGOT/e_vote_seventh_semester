mod rsa {
    use std::ops::Rem;
    use derive_more::Deref;
    use getset::Getters;
    use lazy_static::lazy_static;
    use num_bigint::{BigUint, RandBigInt};
    use num_traits::{One, ToPrimitive, Zero};
    use rand::Rng;
    use serde::{Deserialize, Serialize};
    use thiserror::Error;

    #[derive(Error, Debug)]
    #[error("Failed convert to byte: {0}")]
    pub struct ConvertToBytesError(BigUint);

    pub fn convert_to_bytes(i: &[BigUint]) -> Result<Vec<u8>, ConvertToBytesError> {
        i.iter()
            .try_fold(Vec::new(), |mut acc, unit| {
                unit.to_u8().ok_or_else(|| {
                    ConvertToBytesError(unit.clone())
                }).map(|byte| {
                    acc.push(byte);
                    acc
                })
            })
    }

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

    pub fn cipher_data_biguint(key: &impl KeyRef, mut data: Vec<BigUint>) -> Result<Vec<BigUint>, CipherDataError> {
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

    #[cfg(test)]
    mod tests {
        use num_traits::ToPrimitive;
        use super::{cipher_data_biguint, cipher_data_u8, KeyPair};

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

mod elgamal {
    use num_traits::ToPrimitive;
    use serde::{Deserialize, Serialize};
    use thiserror::Error;
    use num_prime::nt_funcs::is_prime64;
    use rand::distributions::uniform::SampleRange;
    use rand::Rng;

    fn positive_mod(a: i64, n: i64) -> i64 {
        ((a % n) + n) % n
    }

    pub fn modinv(z: u16, a: u16) -> Option<u16> {

        if z == 0 {
            return None;
        }

        if a == 0 || !is_prime64(a as u64) {
            return None;
        }

        if z >= a {
            return None;
        }

        let mut i = a;
        let mut j = z;
        let mut y_2: i64 = 0;
        let mut y_1: i64 = 1;

        while j > 0 {
            let quotient = i / j;
            let remainder = i % j;
            let y = y_2 - (y_1 * quotient as i64);
            i = j;
            j = remainder;
            y_2 = y_1;
            y_1 = y;
        }
        if i != 1 {
            return None;
        }
        Some(positive_mod(y_2, a as i64) as u16)
    }

    pub fn modpow(base: u64, exp: u64, modulus: u64) -> u64 {
        let mut result = 1;
        let mut base = base % modulus;
        let mut exp = exp;

        while exp > 0 {
            if exp % 2 == 1 {
                result = (result * base) % modulus;
            }
            exp >>= 1;
            base = (base * base) % modulus;
        }

        result
    }

    pub fn gen_prime<R: SampleRange<u16> + Clone>(r: R) -> u16 {
        loop {
            let n = rand::thread_rng().gen_range(r.clone());
            if is_prime64(n as u64) {
                break n;
            }
        }
    }

    #[derive(Serialize, Deserialize)]
    pub struct CipheredData {
        pub a: u16,
        pub bs: Vec<u16>
    }

    const MIN_P: u16 = u8::MAX as u16 + 1;
    const MAX_P: u16 = u16::MAX;

    #[derive(Serialize, Deserialize)]
    pub struct PublicKey {
        g: u16,
        y: u16,
        p: u16,
    }

    impl PublicKey {
        pub fn cipher(&self, data: &[u8]) -> CipheredData {
            let (a, u) = {
                let k = rand::thread_rng().gen_range(1..(self.p - 1));
                (
                    modpow(self.g as u64, k as u64, self.p as u64) as u16,
                    modpow(self.y as u64, k as u64, self.p as u64) as u16
                )
            };
            CipheredData {
                a,
                bs: data.iter()
                    .map(|m| {
                        ((u as u32 * (*m as u32)) % self.p as u32) as u16
                    })
                    .collect()
            }
        }
    }

    #[derive(Error, Debug)]
    pub enum DecipherError {
        #[error("Can not create inverse")]
        CanNotCreateInverse{ s: u16, p: u16 },
        #[error("Can not convert to byte")]
        CanNotConvertToByte(u16),
    }

    pub struct PrivateKey {
        p: u16,
        x: u16,
    }

    impl PrivateKey {
        pub fn decipher(&self, c_data: &CipheredData) -> Result<Vec<u8>, DecipherError> {
            let s_inv = {
                let s = modpow(c_data.a as u64, self.x as u64, self.p as u64) as u16;
                modinv(s, self.p).ok_or(DecipherError::CanNotCreateInverse { s, p: self.p })?
            };
            c_data.bs.iter().try_fold(Vec::new(), |mut acc, c| {
                let prob_byte = ((*c as u32 * s_inv as u32) % self.p as u32) as u16;
                let byte = prob_byte.to_u8().ok_or(DecipherError::CanNotConvertToByte(prob_byte))?;
                acc.push(byte);
                Ok(acc)
            })
        }
    }

    pub struct KeyPair {
        pub private_key: PrivateKey,
        pub public_key: PublicKey,
    }

    impl Default for KeyPair {
        fn default() -> Self {
            let p = gen_prime(MIN_P..MAX_P);
            let g = gen_prime(1..p);
            let x = rand::thread_rng().gen_range(1..(p - 2));
            let y = modpow(g as u64, x as u64, p as u64) as u16;
            Self { public_key: PublicKey { g, y, p }, private_key: PrivateKey { p, x } }
        }
    }

    #[cfg(test)]
    mod tests {

        #[test]
        fn it_works() {
            let message = "message";
            let key_pair = super::KeyPair::default();
            let c_data = key_pair.public_key.cipher(message.as_bytes());
            let data = key_pair.private_key.decipher(&c_data).unwrap();
            let deciphered_message = String::from_utf8(data).unwrap();
            assert_eq!(message, deciphered_message);
        }

        #[test]
        fn test_modinv() {
            let vals = [(23, 6577), (10, 7919), (17, 3181)];
            for (z, a) in vals {
                let res = super::modinv(z, a).unwrap();
                let b = z * res;
                let c = b % a;
                assert_eq!(c, 1);
            }
        }
    }
}

mod voter {
    use std::mem;
    use num_bigint::BigUint;
    use num_traits::FromPrimitive;
    use rand::prelude::IteratorRandom;
    use rand::Rng;
    use serde::{Deserialize, Serialize};
    use thiserror::Error;
    use crate::{elgamal, rsa};

    #[derive(Default)]
    struct FirstStageNoise(Vec<BigUint>);

    #[derive(Default)]
    struct SecondStageNoise(Vec<BigUint>);

    #[derive(Default)]
    struct SecondStageNoiseRow(Vec<SecondStageNoise>);

    #[derive(Default)]
    struct SecondStageNoiseTable(Vec<SecondStageNoiseRow>);

    #[derive(Default)]
    struct Voter {
        rsa: rsa::KeyPair,
        elgamal: elgamal::KeyPair,
    }

    fn create_noise(noise_length: usize) -> Vec<BigUint> {
        (0..noise_length).into_iter().map(|_| {
            BigUint::from_u8(rand::thread_rng().gen_range(0u8..u8::MAX)).unwrap()
        }).collect::<Vec<_>>()
    }

    #[derive(Default)]
    struct SecondStageCipherData(Vec<BigUint>);

    pub fn first_stage_cipher<'a, I>(
        candidates: &[Candidate],
        pub_keys: I,
        noise_length: usize,
        mut second_stage_noise_table: SecondStageNoiseTable,
    ) -> Result<(FirstStageNoise, SecondStageNoiseTable, SecondStageCipherData), CipherError>
        where
            I: Iterator<Item = &'a rsa::PublicKeyRef<'a>> + Clone {

        let (first_stage_noise, mut ser_first_stage_cipher_data) = {
            let (first_stage_noise, first_stage_cipher_data) = {
                let (first_stage_noise, cipher_data) = {
                    let candidate = candidates.iter().choose(&mut rand::thread_rng())
                        .ok_or(CipherError::CanNotChooseCandidate)?;
                    let first_stage_noise = FirstStageNoise(create_noise(noise_length));
                    (
                        first_stage_noise,
                        bincode::serialize(&candidate)
                            .map_err(CipherError::SerializeCandidate)?
                            .into_iter()
                            .map(|v| BigUint::from_u8(v).unwrap())
                            .chain(first_stage_noise.0.iter().map(Clone::clone))
                            .collect::<Vec<_>>()
                    )
                };
                (
                    first_stage_noise,
                    FirstStageCipherData(
                        pub_keys.clone()
                            .try_fold(cipher_data, |acc, pub_key_ref| {
                                rsa::cipher_data_biguint(pub_key_ref, acc)
                                    .map_err(CipherError::FirstStageCipherData)
                            })?
                    )
                )
            };
            (
                first_stage_noise,
                bincode::serialize(&first_stage_cipher_data)
                    .map_err(CipherError::SerializeCandidate)?
                    .into_iter()
                    .map(|v| BigUint::from_u8(v).unwrap())
                    .collect::<Vec<BigUint>>()
            )
        };

        for (pub_key, second_stage_noise_row) in pub_keys.zip(second_stage_noise_table.0.iter_mut()) {
            let noise = create_noise(noise_length);
            ser_first_stage_cipher_data.extend(noise.iter().map(Clone::clone));
            second_stage_noise_row.0.push(SecondStageNoise(noise));
            ser_first_stage_cipher_data = rsa::cipher_data_biguint(pub_key, mem::take(&mut ser_first_stage_cipher_data))
                .map_err(CipherError::SecondStageCipherData)?;
        }

        Ok((first_stage_noise, second_stage_noise_table, SecondStageCipherData(ser_first_stage_cipher_data)))
    }

    #[derive(Serialize, Deserialize, Debug, Clone)]
    pub struct Candidate(pub String);

    pub fn sort_voters(voters: &mut Vec<Voter>) {
        voters.sort_by(|a, b| {
            let a_p = a.rsa.get_product_number();
            let b_p = b.rsa.get_product_number();
            a_p.cmp(&b_p)
        });
    }

    #[derive(Error, Debug)]
    pub enum CipherError {
        #[error("Can not chose candidate")]
        CanNotChooseCandidate,
        #[error(transparent)]
        SerializeCandidate(bincode::Error),
        #[error(transparent)]
        FirstStageCipherData(rsa::CipherDataError),
        #[error(transparent)]
        SerializeFirstStageCipherData(bincode::Error),
        #[error(transparent)]
        SecondStageCipherData(rsa::CipherDataError),
    }

    #[derive(Serialize, Deserialize)]
    struct FirstStageCipherData(Vec<BigUint>);

    fn decipher_second_stage_cipher_data(

    ) {

    }



    #[cfg(test)]
    mod tests {
        use std::mem;
        use num_traits::ToPrimitive;
        use crate::rsa;
        use crate::voter::{first_stage_cipher, sort_voters, Candidate, FirstStageCipherData, SecondStageNoiseTable, Voter};

        #[test]
        fn it_works() {
            let noise_length = 20usize;

            let mut voters = (0..10).into_iter().map(|_| Voter::default())
                .collect::<Vec<_>>();
            sort_voters(&mut voters);

            let candidates = (0..100).into_iter().map(|i| Candidate(i.to_string()))
                .collect::<Vec<_>>();

            let (first_stage_noises, second_stage_noise_table, second_stage_cipher_datas) = {
                let mut first_stage_noises = Vec::new();
                let mut second_stage_noises = SecondStageNoiseTable(Vec::new());
                let mut second_stage_cipher_datas = Vec::new();
                let public_keys = voters.iter().map(|v| v.rsa.get_public_key_ref());

                for _ in &voters {
                    let res = first_stage_cipher(&candidates, public_keys.clone(), noise_length, mem::take(&mut second_stage_noises))
                        .unwrap();
                    first_stage_noises.push(res.0);
                    second_stage_noises = res.1;
                    second_stage_cipher_datas.push(res.2);
                }
                (first_stage_noises, second_stage_noises, second_stage_cipher_datas)
            };

            {
                let private_keys = voters.iter().map(|v| v.rsa.get_private_key_ref());

                let mut first_stage_cipher_datas = Vec::new();

                for (second_stage_cipher_data, second_stage_noise_row) in second_stage_cipher_datas
                    .into_iter().zip(second_stage_noise_table.0.into_iter()) {

                    let mut data = second_stage_cipher_data.0;
                    for (private_key, second_stage_noise) in private_keys
                        .clone().zip(second_stage_noise_row.0.into_iter()).rev() {

                        data = rsa::cipher_data_biguint(&private_key, mem::take(&mut data)).unwrap();
                        assert!(data.len() > second_stage_noise.0.len());
                        second_stage_noise.0.iter().rev()
                            .zip(data.iter().rev())
                            .for_each(|(a, b)| assert_eq!(a, b));
                        let data_len = data.len();
                        data = mem::take(&mut data).into_iter()
                            .take(data_len - second_stage_noise.0.len())
                            .collect::<Vec<_>>();
                    }
                    let byte_data = data.into_iter().map(|v| v.to_u8().unwrap())
                        .collect::<Vec<_>>();

                    first_stage_cipher_datas.push(
                        bincode::deserialize::<FirstStageCipherData>(&byte_data).unwrap()
                    );
                }
            }

        }
    }

}

