mod alg_utils {
    use num_prime::nt_funcs::is_prime64;
    use rand::distributions::uniform::SampleRange;
    use rand::Rng;

    fn positive_mod<T: num_integer::Integer + Copy>(a: T, n: T) -> T {
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

    #[cfg(test)]
    mod tests {
        use super::modinv;

        #[test]
        fn it_works() {
            let vals = [(23, 6577), (10, 7919), (17, 3181)];
            for (z, a) in vals {
                let res = modinv(z, a).unwrap();
                let b = z * res;
                let c = b % a;
                assert_eq!(c, 1);
            }
        }
    }
}


mod dsa {
    use std::hash::{DefaultHasher, Hasher};
    use std::ops::Rem;
    use rand::Rng;
    use crate::alg_utils::{gen_prime, modinv, modpow};
    use num_prime::nt_funcs::is_prime64;

    fn calculate_hash(data: &[u8]) -> u16 {
        let mut hasher = DefaultHasher::new();
        hasher.write(data);
        hasher.finish() as u16
    }

    pub struct Dsa {
        q: u16,
        p: u64,
        g: u64,
        x: u16,
        y: u64,
    }

    pub struct Signature {
        r: u16,
        s: u16,
    }

    impl Dsa {
        pub fn new() -> Self {
            let (q, p) = 'qp_loop: loop {
                const N: usize = 16;
                const MIN: u16 = (1 << (N - 1)) as u16;
                const MAX: u16 = ((1 << N) - 1) as u16;
                let q = gen_prime(MIN..MAX);
                let mut p_1 = (q as u64) * 2;
                loop {
                    if u64::MAX - p_1 < q as u64 {
                        continue 'qp_loop;
                    }
                    let p = p_1 + 1;
                    if is_prime64(p) && p_1 % q as u64 == 0 {
                        break 'qp_loop (q, p);
                    }
                    p_1 += q as u64;
                }
            };

            let g = loop {
                let h = rand::thread_rng().gen_range(1..p-1);
                let g = modpow(h, (p - 1) / q as u64, p);
                if g > 1 {
                    break g;
                }
            };

            let x = rand::thread_rng().gen_range(0..q);
            let y = modpow(g, x as u64, p);
            Self { p, q, g, x, y }
        }

        pub fn sign(&self, data: &[u8]) -> Signature {
            let data_hash = calculate_hash(data);
            loop {
                let k = rand::thread_rng().gen_range(0..self.q);
                let r = modpow(self.g, k as u64, self.p).rem(self.q as u64) as u16;
                if r != 0 {
                    if let Some(k_inv) = modinv(k, self.q) {
                        let part = ((data_hash as u64 + self.x as u64 * r as u64) % self.q as u64) as u16;
                        let s = ((k_inv as u64 * part as u64) % self.q as u64) as u16;
                        if s != 0 {
                            break Signature { r, s };
                        }
                    }
                }
            }
        }
    }

    pub fn verify(dsa: &Dsa, signature: &Signature, data: &[u8]) -> bool {
        if ![signature.s, signature.r].iter().all(|num| {
            *num > 0 && *num < dsa.q
        }) {
            return false;
        }
        if let Some(w) = modinv(signature.s, dsa.q) {
            let data_hash = calculate_hash(data);
            let u_one = (data_hash as u64 * w as u64).rem(dsa.q as u64) as u16;
            let u_two = (signature.r as u64 * w as u64).rem(dsa.q as u64) as u16;
            let v_one = modpow(dsa.g, u_one as u64, dsa.p) as u128;
            let v_two = modpow(dsa.y, u_two as u64, dsa.p) as u128;
            let v = ((((v_one * v_two) % dsa.p as u128) as u64) % dsa.q as u64) as u16;
            v == signature.r
        } else {
            false
        }
    }

    #[cfg(test)]
    mod tests {

        #[test]
        fn it_works() {
            let message = "message";
            let dsa = super::Dsa::new();
            let signature = dsa.sign(message.as_bytes());
            let res = super::verify(&dsa, &signature, message.as_bytes());
            assert!(res);
        }
    }
}

mod elgamal {
    use num_traits::ToPrimitive;
    use rand::Rng;
    use thiserror::Error;
    use crate::alg_utils::{gen_prime, modinv, modpow};
    use crate::elgamal::DecipherError::CanNotConvertToByte;

    pub struct CipheredData {
        a: u16,
        bs: Vec<u16>
    }

    const MIN_P: u16 = u8::MAX as u16 + 1;
    const MAX_P: u16 = u16::MAX;

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
                let byte = prob_byte.to_u8().ok_or(CanNotConvertToByte(prob_byte))?;
                acc.push(byte);
                Ok(acc)
            })
        }
    }

    pub fn create_keys() -> (PublicKey, PrivateKey) {
        let p = gen_prime(MIN_P..MAX_P);
        let g = gen_prime(1..p);
        let x = rand::thread_rng().gen_range(1..(p - 2));
        let y = modpow(g as u64, x as u64, p as u64) as u16;
        (PublicKey { g, y, p }, PrivateKey { p, x })
    }

    #[cfg(test)]
    mod tests {

        #[test]
        fn it_works() {
            let message = "message";
            let (public_key, private_key) = super::create_keys();
            let c_data = public_key.cipher(message.as_bytes());
            let data = private_key.decipher(&c_data).unwrap();
            let deciphered_message = String::from_utf8(data).unwrap();
            assert_eq!(message, deciphered_message);
        }
    }
}