mod alg_utils {
    use num_prime::nt_funcs::is_prime64;
    use rand::distributions::uniform::SampleRange;
    use rand::Rng;
    use thiserror::Error;

    pub fn gen_prime<R: SampleRange<u16> + Clone>(r: R) -> u16 {
        loop {
            let n = rand::thread_rng().gen_range(r.clone());
            if is_prime64(n as u64) {
                break n;
            }
        }
    }

    pub fn positive_mod(a: i64, n: i64) -> i64 {
        ((a % n) + n) % n
    }

    #[derive(Error, Debug)]
    #[error("Can not get inverse: {z}, {a}")]
    pub struct ModInvError { z: u16, a: u16 }

    pub fn modinv(z: u16, a: u16) -> Result<u16, ModInvError> {

        if z == 0 {
            return Err(ModInvError {z, a});
        }

        if a == 0 {
            return Err(ModInvError {z, a});
        }

        if z >= a {
            return Err(ModInvError {z, a});
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
            return Err(ModInvError {z, a});
        }
        Ok(positive_mod(y_2, a as i64) as u16)
    }
}

mod elgamal {
    use std::hash::{DefaultHasher, Hasher};
    use std::ops::Rem;
    use num_bigint::BigUint;
    use num_traits::{Pow, ToPrimitive};
    use serde::{Deserialize, Serialize};
    use thiserror::Error;
    use num_prime::nt_funcs::is_prime64;
    use rand::distributions::uniform::SampleRange;
    use rand::Rng;
    use crate::alg_utils;
    use crate::alg_utils::{modinv, positive_mod, ModInvError};

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

    #[derive(Serialize, Deserialize)]
    pub struct CipheredData {
        pub a: u16,
        pub bs: Vec<u16>
    }

    const MIN_P: u16 = u8::MAX as u16 + 1;
    const MAX_P: u16 = u16::MAX;

    #[derive(Serialize, Deserialize, Clone)]
    pub struct PublicKey {
        g: u16,
        y: u16,
        p: u16,
    }

    fn generate_k(p: u16) -> u16 {
        rand::thread_rng().gen_range(1..(p - 1))
    }

    impl PublicKey {
        pub fn cipher(&self, data: &[u8]) -> CipheredData {
            let (a, u) = {
                let k = generate_k(self.p);
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

        pub fn verify(&self, data: &[u8], signature: &Signature) -> bool {
            let y = BigUint::from(self.y);
            let r = BigUint::from(signature.r);
            let left = (y.pow(&r) * r.pow(signature.s)).rem(BigUint::from(self.p)).to_u16().unwrap();

            let m = calculate_hash(data);
            let right = modpow(self.g as u64, m as u64, self.p as u64) as u16;

            let is_valid = left == right;
            is_valid
        }
    }

    #[derive(Error, Debug)]
    pub enum DecipherError {
        #[error("Can not create inverse")]
        ModInv(ModInvError),
        #[error("Can not convert to byte")]
        CanNotConvertToByte(u16),
    }

    #[derive(Clone)]
    pub struct PrivateKey {
        p: u16,
        g: u16,
        y: u16,
        x: u16,
    }

    fn calculate_hash(data: &[u8]) -> u16 {
        let mut hasher = DefaultHasher::new();
        hasher.write(data);
        hasher.finish() as u16
    }

    pub struct Signature{ r: u16, s: u16 }

    impl PrivateKey {
        pub fn decipher(&self, c_data: &CipheredData) -> Result<Vec<u8>, DecipherError> {
            let s_inv = {
                let s = modpow(c_data.a as u64, self.x as u64, self.p as u64) as u16;
                modinv(s, self.p).map_err(DecipherError::ModInv)?
            };
            c_data.bs.iter().try_fold(Vec::new(), |mut acc, c| {
                let prob_byte = ((*c as u32 * s_inv as u32) % self.p as u32) as u16;
                let byte = prob_byte.to_u8().ok_or(DecipherError::CanNotConvertToByte(prob_byte))?;
                acc.push(byte);
                Ok(acc)
            })
        }

        pub fn sign(&self, data: &[u8]) -> Signature {
            let m = calculate_hash(data);
            let (k, k_inv) = loop {
                let k = generate_k(self.p);
                if let Ok(k_inv) = modinv(k, self.p - 1) {
                    break (k, k_inv);
                }
            };
            let r = modpow(self.g as u64, k as u64, self.p as u64) as i64;
            let s = positive_mod((m as i64 - (self.x as i64) * r) * (k_inv as i64), self.p as i64 - 1);
            Signature { r: r as u16, s: s as u16 }
        }
    }

    #[derive(Clone)]
    pub struct KeyPair {
        pub private_key: PrivateKey,
        pub public_key: PublicKey,
    }

    impl Default for KeyPair {
        fn default() -> Self {
            let p = alg_utils::gen_prime(MIN_P..MAX_P);
            let g = alg_utils::gen_prime(1..p);
            let x = rand::thread_rng().gen_range(1..(p - 2));
            let y = modpow(g as u64, x as u64, p as u64) as u16;
            Self { public_key: PublicKey { g, y, p }, private_key: PrivateKey { p, g, y, x } }
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

        #[test]
        fn sign_verify() {
            let message = "message";
            let key_pair = super::KeyPair::default();
            let signature = key_pair.private_key.sign(message.as_bytes());
            let is_valid = key_pair.public_key.verify(message.as_ref(), &signature);
            assert!(is_valid);
        }
    }
}

mod bbs {
    use getset::Getters;
    use num_integer::{lcm, gcd};
    use rand::Rng;
    use crate::alg_utils::{gen_prime, modinv};
    use crate::elgamal::{modpow, CipheredData};

    #[derive(Getters)]
    #[get = "pub with_prefix"]
    pub struct KeyPair {
        public_key: PublicKey,
        private_key: PrivateKey,
    }

    pub struct PrivateKey {
        p: u16,
        q: u16,
    }

    pub struct PublicKey(u32);

    impl Default for KeyPair {

        fn default() -> Self {
            fn gen_prime_34() -> u16 {
                loop {
                    let p = gen_prime(u8::MAX as u16..u16::MAX);
                    if p % 4 == 3 {
                        break p;
                    }
                }
            }

            let p = gen_prime_34();
            let q = gen_prime_34();
            Self {
                public_key: PublicKey((p as u32) * (q as u32)),
                private_key: PrivateKey{ p, q },
            }
        }
    }

    macro_rules! get_last_bit {
        ($v:expr) => {
            v & 1 == 1
        };
    }

    const fn u8_to_bits(mut v: u8) -> [bool; 8] {
        std::array::from_fn(|_| {
            let b = get_last_bit!(v);
            v >>= 1;
            b
        })
    }

    const fn bits_to_u8(bits: [bool; 8]) -> u8 {
        let mut a: u8 = 0;
        for b in bits {
            let ba = b as u8;
            a |= ba;
            a <<= 1;
        }
        a
    }

    impl PublicKey {
        pub fn cipher(&self, data: &mut [u8]) -> u32 {
            let x = loop {
                let x = rand::thread_rng().gen_range(0..self.0);
                if gcd(x as u64, self.0 as u64) == 1 {
                    break x;
                }
            };
            let next_x = |x: u64| {
                ((x * x) % (self.0 as u64)) as u32
            };
            let x_0 = next_x(x as u64);
            let mut x = x_0;
            data.iter_mut().for_each(|v| {
                let bits = u8_to_bits(*v);
                let xor_bits: [bool; 8] = std::array::from_fn(|i| {
                    let b = bits[i] ^ get_last_bit!(x);
                    x = next_x(x as u64);
                    b
                });
                *v = bits_to_u8(xor_bits);
            });
            x_0
        }
    }

    impl PrivateKey {
        pub fn decipher(&self, data: &mut [u8], x_0: u32) {
            let lcm_lam = lcm(self.p - 1, self.q - 1);
            let n = self.p as u32 * self.q as u32;
            let next_x = |i: usize| {
                let ppow = modpow(2, i as u64, lcm_lam as u64);
                modpow(x_0 as u64, ppow, n as u64) as u32
            };
            let mut x = next_x(0);
            let mut x_index = 1;
            data.iter_mut().for_each(|v| {
                let bits = u8_to_bits(*v);
                let xor_bits: [bool; 8] = std::array::from_fn(|i| {
                    let b = bits[i] ^ get_last_bit!(x);
                    x = next_x(x_index);
                    x_index += 1;
                    b
                });
                *v = bits_to_u8(xor_bits);
            });
        }
    }

}