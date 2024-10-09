use std::hash::{DefaultHasher, Hasher};
use num_integer::Roots;
use num_prime::nt_funcs::is_prime64;
use num_traits::Num;
use num_traits::real::Real;
use rand::Rng;
use num_prime::RandPrime;

fn calculate_hash(data: &[u8]) -> u16 {
    let mut hasher = DefaultHasher::new();
    hasher.write(data);
    hasher.finish() as u16
}

fn positive_mod<T: num_integer::Integer + Copy>(a: T, n: T) -> T {
    ((a % n) + n) % n
}

fn modinv(z: u16, a: u16) -> Option<u16> {

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

#[cfg(test)]
mod tests {
    use crate::modinv;

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



fn modpow(base: u64, exp: u64, modulus: u64) -> u64 {
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

fn min_bits_number(number: u64) -> u8 {
    const MASK: u64 = 1 << 63;
    let mut number = number;
    let mut zeros = 0u8;
    while number & MASK == 0 {
        number <<= 1;
        zeros += 1;
    }
    64 - zeros
}

mod dsa {
    use std::ops::Rem;
    use num_bigint::{BigUint, RandBigInt};
    use num_prime::RandPrime;
    use num_traits::{One, Pow, ToPrimitive, Zero};
    use rand::Rng;
    use crate::{calculate_hash, modinv, modpow};
    use num_prime::nt_funcs::is_prime64;

    struct DSA {
        q: u16,
        p: u64,
        g: u64,
        x: u16,
        y: u64,
    }

    struct Signature {
        r: u16,
        s: u16,
    }

    impl DSA {
        pub fn new() -> Self {
            let (q, p) = 'qp_loop: loop {
                const N: usize = 16;
                const MIN: u16 = (1 << (N - 1)) as u16;
                const MAX: u16 = ((1 << N) - 1) as u16;
                let q = loop {
                    let q = rand::thread_rng().gen_range(MIN..MAX);
                    if is_prime64(q as u64) {
                        break q;
                    }
                };
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

    pub fn verify(dsa: &DSA, signature: &Signature, data: &[u8]) -> bool {
        if ![signature.s, signature.r].iter().all(|num| {
            *num > 0 && *num < dsa.q
        }) {
            return false;
        }

        let w = modinv(signature.s, dsa.q).unwrap();
        let data_hash = calculate_hash(data);
        let u_one = (data_hash as u64 * w as u64).rem(dsa.q as u64) as u16;
        let u_two = (signature.r as u64 * w as u64).rem(dsa.q as u64) as u16;
        let v_one = modpow(dsa.g, u_one as u64, dsa.p) as u128;
        let v_two = modpow(dsa.y, u_two as u64, dsa.p) as u128;
        let v = ((((v_one * v_two) % dsa.p as u128) as u64) % dsa.q as u64) as u16;
        v == signature.r
    }

    #[cfg(test)]
    mod tests {
        use crate::{dsa};

        #[test]
        fn it_works() {
            let message = "message";
            let dsa = dsa::DSA::new();
            let signature = dsa.sign(message.as_bytes());
            let res = dsa::verify(&dsa, &signature, message.as_bytes());
            assert!(res);
        }
    }
}