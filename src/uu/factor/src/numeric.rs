// * This file is part of the uutils coreutils package.
// *
// * (c) 2015 Wiktor Kuropatwa <wiktor.kuropatwa@gmail.com>
// * (c) 2020 nicoo            <nicoo@debian.org>
// *
// * For the full copyright and license information, please view the LICENSE file
// * that was distributed with this source code.

use num_traits::{
    int::PrimInt,
    ops::wrapping::{WrappingMul, WrappingSub},
};
use std::fmt::Debug;
use std::mem::swap;

// This is incorrectly reported as dead code,
//  presumably when included in build.rs.
#[allow(dead_code)]
pub(crate) fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b > 0 {
        a %= b;
        swap(&mut a, &mut b);
    }
    a
}

pub(crate) trait Arithmetic: Copy + Sized {
    type I: Copy + Sized + Eq;

    fn new(m: u64) -> Self;
    fn modulus(&self) -> u64;
    fn from_u64(&self, n: u64) -> Self::I;
    fn to_u64(&self, n: Self::I) -> u64;
    fn add(&self, a: Self::I, b: Self::I) -> Self::I;
    fn mul(&self, a: Self::I, b: Self::I) -> Self::I;

    fn pow(&self, mut a: Self::I, mut b: u64) -> Self::I {
        let (_a, _b) = (a, b);
        let mut result = self.one();
        while b > 0 {
            if b & 1 != 0 {
                result = self.mul(result, a);
            }
            a = self.mul(a, a);
            b >>= 1;
        }

        // Check that r (reduced back to the usual representation) equals
        //  a^b % n, unless the latter computation overflows
        // Temporarily commented-out, as there u64::checked_pow is not available
        //  on the minimum supported Rust version, nor is an appropriate method
        //  for compiling the check conditionally.
        //debug_assert!(self
        //    .to_u64(_a)
        //    .checked_pow(_b as u32)
        //    .map(|r| r % self.modulus() == self.to_u64(result))
        //    .unwrap_or(true));

        result
    }

    fn one(&self) -> Self::I {
        self.from_u64(1)
    }
    fn minus_one(&self) -> Self::I {
        self.from_u64(self.modulus() - 1)
    }
    fn zero(&self) -> Self::I {
        self.from_u64(0)
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Montgomery {
    a: u64,
    n: u64,
}

impl Montgomery {
    /// computes x/R mod n efficiently
    fn reduce(&self, x: u128) -> u64 {
        debug_assert!(x < (self.n as u128) << 64);
        // TODO: optimiiiiiiise
        let Montgomery { a, n } = self;
        let m = (x as u64).wrapping_mul(*a);
        let nm = (*n as u128) * (m as u128);
        let (xnm, overflow) = (x as u128).overflowing_add(nm); // x + n*m
        debug_assert_eq!(xnm % (1 << 64), 0);

        // (x + n*m) / R
        // in case of overflow, this is (2¹²⁸ + xnm)/2⁶⁴ - n = xnm/2⁶⁴ + (2⁶⁴ - n)
        let y = (xnm >> 64) as u64 + if !overflow { 0 } else { n.wrapping_neg() };

        if y >= *n {
            y - n
        } else {
            y
        }
    }
}

impl Arithmetic for Montgomery {
    // Montgomery transform, R=2⁶⁴
    // Provides fast arithmetic mod n (n odd, u64)
    type I = u64;

    fn new(n: u64) -> Self {
        let a = modular_inverse(n).wrapping_neg();
        debug_assert_eq!(n.wrapping_mul(a), 1_u64.wrapping_neg());
        Montgomery { a, n }
    }

    fn modulus(&self) -> u64 {
        self.n
    }

    fn from_u64(&self, x: u64) -> Self::I {
        // TODO: optimise!
        assert!(x < self.n);
        let r = (((x as u128) << 64) % self.n as u128) as u64;
        debug_assert_eq!(x, self.to_u64(r));
        r
    }

    fn to_u64(&self, n: Self::I) -> u64 {
        self.reduce(n as u128)
    }

    fn add(&self, a: Self::I, b: Self::I) -> Self::I {
        let (r, overflow) = a.overflowing_add(b);

        // In case of overflow, a+b = 2⁶⁴ + r = (2⁶⁴ - n) + r (working mod n)
        let r = if !overflow {
            r
        } else {
            r + self.n.wrapping_neg()
        };

        // Normalise to [0; n[
        let r = if r < self.n { r } else { r - self.n };

        // Check that r (reduced back to the usual representation) equals
        // a+b % n
        #[cfg(debug_assertions)]
        {
            let a_r = self.to_u64(a);
            let b_r = self.to_u64(b);
            let r_r = self.to_u64(r);
            let r_2 = (((a_r as u128) + (b_r as u128)) % (self.n as u128)) as u64;
            debug_assert_eq!(
                r_r, r_2,
                "[{}] = {} ≠ {} = {} + {} = [{}] + [{}] mod {}; a = {}",
                r, r_r, r_2, a_r, b_r, a, b, self.n, self.a
            );
        }
        r
    }

    fn mul(&self, a: Self::I, b: Self::I) -> Self::I {
        let r = self.reduce((a as u128) * (b as u128));

        // Check that r (reduced back to the usual representation) equals
        // a*b % n
        #[cfg(debug_assertions)]
        {
            let a_r = self.to_u64(a);
            let b_r = self.to_u64(b);
            let r_r = self.to_u64(r);
            let r_2 = (((a_r as u128) * (b_r as u128)) % (self.n as u128)) as u64;
            debug_assert_eq!(
                r_r, r_2,
                "[{}] = {} ≠ {} = {} * {} = [{}] * [{}] mod {}; a = {}",
                r, r_r, r_2, a_r, b_r, a, b, self.n, self.a
            );
        }
        r
    }
}

pub(crate) trait Int: Debug + PrimInt + WrappingSub + WrappingMul {}
impl Int for u64 {}
impl Int for u32 {}

// extended Euclid algorithm
// precondition: a is odd
pub(crate) fn modular_inverse<T: Int>(a: T) -> T {
    let zero = T::zero();
    let one = T::one();
    assert!(a % (one + one) == one, "{:?} is not odd", a);

    let mut t = zero;
    let mut newt = one;
    let mut r = zero;
    let mut newr = a;

    while newr != zero {
        let quot = if r == zero {
            // special case when we're just starting out
            // This works because we know that
            // a does not divide 2^64, so floor(2^64 / a) == floor((2^64-1) / a);
            T::max_value()
        } else {
            r
        } / newr;

        let newtp = t.wrapping_sub(&quot.wrapping_mul(&newt));
        t = newt;
        newt = newtp;

        let newrp = r.wrapping_sub(&quot.wrapping_mul(&newr));
        r = newr;
        newr = newrp;
    }

    assert_eq!(r, one);
    t
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Montgomery32 {
    a: u32,
    n: u32,
}

impl Montgomery32 {
    /// computes x/R mod n efficiently
    fn reduce(&self, x: u64) -> u32 {
        debug_assert!(x < (self.n as u64) << 32);
        // TODO: optimiiiiiiise
        let Montgomery32 { a, n } = self;
        let m = (x as u32).wrapping_mul(*a);
        let nm = (*n as u64) * (m as u64);
        let (xnm, overflow) = x.overflowing_add(nm); // x + n*m
        debug_assert_eq!(xnm % (1 << 32), 0);

        // (x + n*m) / R
        // in case of overflow, this is (2¹²⁸ + xnm)/2⁶⁴ - n = xnm/2⁶⁴ + (2⁶⁴ - n)
        let y = (xnm >> 32) as u32 + if !overflow { 0 } else { n.wrapping_neg() };

        if y >= *n {
            y - n
        } else {
            y
        }
    }
}

impl Arithmetic for Montgomery32 {
    // Montgomery transform, R=2⁶⁴
    // Provides fast arithmetic mod n (n odd, u64)
    type I = u32;

    fn new(n: u64) -> Self {
        debug_assert!(n < (1 << 32));
        let n = n as u32;
        let a = modular_inverse(n).wrapping_neg();
        debug_assert_eq!(n.wrapping_mul(a), 1_u32.wrapping_neg());
        Montgomery32 { a, n }
    }

    fn modulus(&self) -> u64 {
        self.n as u64
    }

    fn from_u64(&self, x: u64) -> Self::I {
        assert!(x < self.n as u64);
        let r = ((x << 32) % self.n as u64) as u32;
        debug_assert_eq!(x, self.to_u64(r));
        r
    }

    fn to_u64(&self, n: Self::I) -> u64 {
        self.reduce(n as u64) as u64
    }

    fn add(&self, a: Self::I, b: Self::I) -> Self::I {
        let (r, overflow) = a.overflowing_add(b);

        // In case of overflow, a+b = 2⁶⁴ + r = (2⁶⁴ - n) + r (working mod n)
        let r = if !overflow {
            r
        } else {
            r + self.n.wrapping_neg()
        };

        // Normalise to [0; n[
        let r = if r < self.n { r } else { r - self.n };

        // Check that r (reduced back to the usual representation) equals
        // a+b % n
        #[cfg(debug_assertions)]
        {
            let a_r = self.to_u64(a);
            let b_r = self.to_u64(b);
            let r_r = self.to_u64(r);
            let r_2 = (((a_r as u128) + (b_r as u128)) % (self.n as u128)) as u64;
            debug_assert_eq!(
                r_r, r_2,
                "[{}] = {} ≠ {} = {} + {} = [{}] + [{}] mod {}; a = {}",
                r, r_r, r_2, a_r, b_r, a, b, self.n, self.a
            );
        }
        r
    }

    fn mul(&self, a: Self::I, b: Self::I) -> Self::I {
        let r = self.reduce((a as u64) * (b as u64));

        // Check that r (reduced back to the usual representation) equals
        // a*b % n
        #[cfg(debug_assertions)]
        {
            let a_r = self.to_u64(a);
            let b_r = self.to_u64(b);
            let r_r = self.to_u64(r);
            let r_2 = (a_r * b_r) % (self.n as u64);
            debug_assert_eq!(
                r_r, r_2,
                "[{}] = {} ≠ {} = {} * {} = [{}] * [{}] mod {}; a = {}",
                r, r_r, r_2, a_r, b_r, a, b, self.n, self.a
            );
        }
        r
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_inverter<T: Int>() {
        // All odd integers from 1 to 20 000
        let one = T::from(1).unwrap();
        let two = T::from(2).unwrap();
        let mut test_values = (0..10_000)
            .map(|i| T::from(i).unwrap())
            .map(|i| two * i + one);

        assert!(test_values.all(|x| x.wrapping_mul(&modular_inverse(x)) == one));
    }

    #[test]
    fn test_inverter_u32() {
        test_inverter::<u32>()
    }

    #[test]
    fn test_inverter_u64() {
        test_inverter::<u64>()
    }

    #[test]
    fn test_montgomery_add() {
        for n in 0..100 {
            let n = 2 * n + 1;
            let m = Montgomery::new(n);
            for x in 0..n {
                let m_x = m.from_u64(x);
                for y in 0..=x {
                    let m_y = m.from_u64(y);
                    println!("{n:?}, {x:?}, {y:?}", n = n, x = x, y = y);
                    assert_eq!((x + y) % n, m.to_u64(m.add(m_x, m_y)));
                }
            }
        }
    }

    #[test]
    fn test_montgomery_mult() {
        for n in 0..100 {
            let n = 2 * n + 1;
            let m = Montgomery::new(n);
            for x in 0..n {
                let m_x = m.from_u64(x);
                for y in 0..=x {
                    let m_y = m.from_u64(y);
                    assert_eq!((x * y) % n, m.to_u64(m.mul(m_x, m_y)));
                }
            }
        }
    }

    #[test]
    fn test_montgomery_roundtrip() {
        for n in 0..100 {
            let n = 2 * n + 1;
            let m = Montgomery::new(n);
            for x in 0..n {
                let x_ = m.from_u64(x);
                assert_eq!(x, m.to_u64(x_));
            }
        }
    }
}
