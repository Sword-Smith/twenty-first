use crate::shared_math::traits::{IdentityValues, ModPowU64, New};
use crate::utils::{FIRST_TEN_THOUSAND_PRIMES, FIRST_THOUSAND_PRIMES};
use num_bigint::BigInt;
use num_traits::One;
use num_traits::Zero;
use serde::Serialize;
use std::convert::Into;
use std::hash::Hash;
use std::ops::Add;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Neg;
use std::ops::Rem;
use std::ops::Sub;
use std::{fmt, vec};

use super::traits::FieldBatchInversion;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Hash)]
pub struct PrimeFieldBig {
    pub q: BigInt,
}

impl PrimeFieldBig {
    pub fn new(q: BigInt) -> Self {
        Self { q }
    }

    pub fn ring_zero(&self) -> PrimeFieldElementBig {
        PrimeFieldElementBig {
            value: 0.into(),
            field: self,
        }
    }

    pub fn ring_one(&self) -> PrimeFieldElementBig {
        PrimeFieldElementBig {
            value: 1.into(),
            field: self,
        }
    }

    pub fn from_bytes(&self, bytes: &[u8]) -> PrimeFieldElementBig {
        PrimeFieldElementBig::from_bytes(self, bytes)
    }

    // Verify that field prime is of the form a*k + b
    // where a, b, and k are all integers
    pub fn prime_check(&self, a: BigInt, b: BigInt) -> bool {
        self.q.clone() % a == b
    }

    pub fn get_generator_values<'a>(
        &self,
        generator: &PrimeFieldElementBig<'a>,
        length: usize,
    ) -> Vec<PrimeFieldElementBig<'a>> {
        let mut output: Vec<PrimeFieldElementBig> = vec![];
        let mut value: PrimeFieldElementBig = generator.ring_one();
        for _ in 0..length {
            output.push(value.clone());
            value = value.clone() * generator.clone();
        }

        output
    }

    pub fn get_power_series(&self, root: BigInt) -> Vec<BigInt> {
        let mut val: BigInt = root.clone();
        let mut ret: Vec<BigInt> = vec![BigInt::one()];

        // Idiomatic way of constructing a do-while loop in Rust
        loop {
            ret.push(val.clone());
            val = val.clone() * root.clone() % self.q.clone();
            if val.is_one() {
                break;
            }
        }
        ret
    }

    pub fn get_field_with_primitive_root_of_unity(
        n: i128,
        min_value: i128,
        ret: &mut Option<(Self, BigInt)>,
    ) {
        // Notice here that the type annotation is on the trait `Into`
        // and not on the function `into`.
        let primes: Vec<BigInt> = FIRST_TEN_THOUSAND_PRIMES
            .iter()
            .filter(|&x| *x > min_value)
            .map(|x| Into::<BigInt>::into(*x))
            .collect::<Vec<BigInt>>();
        for prime in primes.iter() {
            let field = PrimeFieldBig::new(prime.to_owned());
            if let (Some(j), _) = field.get_primitive_root_of_unity(n) {
                *ret = Some((PrimeFieldBig::new(prime.to_owned()), j.value));
                return;
            }
        }
        *ret = None;
    }

    pub fn evaluate_straight_line(
        &self,
        (a, b): (PrimeFieldElementBig, PrimeFieldElementBig),
        x_values: &[PrimeFieldElementBig],
    ) -> Vec<PrimeFieldElementBig> {
        let values = x_values
            .iter()
            .map(|x| (x.to_owned() * a.clone() + b.clone()).value)
            .collect::<Vec<BigInt>>();
        values
            .iter()
            .map(|x| PrimeFieldElementBig::new(x.to_owned(), self))
            .collect::<Vec<PrimeFieldElementBig>>()
    }

    pub fn lagrange_interpolation_2(
        &self,
        point0: (PrimeFieldElementBig, PrimeFieldElementBig),
        point1: (PrimeFieldElementBig, PrimeFieldElementBig),
    ) -> (PrimeFieldElementBig, PrimeFieldElementBig) {
        let x_diff = point0.0.clone() - point1.0.clone();
        let x_diff_inv = x_diff.inv();
        let a = (point0.1.clone() - point1.1.clone()) * x_diff_inv;
        let b = point0.1.clone() - a.clone() * point0.0.clone();
        (
            PrimeFieldElementBig::new(a.value, self),
            PrimeFieldElementBig::new(b.value, self),
        )
    }

    pub fn batch_inversion(&self, nums: Vec<BigInt>) -> Vec<BigInt> {
        // TODO: Panic on 0
        // Adapted from https://paulmillr.com/posts/noble-secp256k1-fast-ecc/#batch-inversion
        let size = nums.len();
        if size == 0 {
            return Vec::<BigInt>::new();
        }

        let mut scratch: Vec<BigInt> = vec![BigInt::zero(); size];
        let mut acc = BigInt::one();
        scratch[0] = nums[0].clone();
        for i in 0..size {
            assert!(!nums[i].is_zero(), "Cannot do batch inversion on zero");
            scratch[i] = acc.clone();
            acc = acc.clone() * nums[i].clone() % self.q.clone()
        }

        // Invert the last element of the `partials` vector
        let (_, inv, _) = PrimeFieldElementBig::eea(acc, self.q.clone());
        acc = inv;
        let mut res = nums;
        for i in (0..size).rev() {
            let tmp = acc.clone() * res[i].clone() % self.q.clone();
            res[i] = (acc.clone() * scratch[i].clone() % self.q.clone() + self.q.clone())
                % self.q.clone();
            acc = tmp;
        }

        res
    }

    pub fn batch_inversion_elements(
        &self,
        input: Vec<PrimeFieldElementBig>,
    ) -> Vec<PrimeFieldElementBig> {
        let values = input
            .iter()
            .map(|x| x.value.clone())
            .collect::<Vec<BigInt>>();
        let result_values = self.batch_inversion(values);
        result_values
            .iter()
            .map(|x| PrimeFieldElementBig::new(x.to_owned(), self))
            .collect::<Vec<PrimeFieldElementBig>>()
    }

    pub fn get_primitive_root_of_unity(
        &self,
        n: i128,
    ) -> (Option<PrimeFieldElementBig>, Vec<BigInt>) {
        let mut primes: Vec<i128> = vec![];

        if n <= 1 {
            let primes_bigint = primes
                .iter()
                .map(|x| Into::<BigInt>::into(*x))
                .collect::<Vec<BigInt>>();
            return (
                Some(PrimeFieldElementBig::new(BigInt::one(), self)),
                primes_bigint,
            );
        }

        // Calculate prime factorization of n
        // Check if n = 2^k
        if n & (n - 1) == 0 {
            primes = vec![2];
        } else {
            let mut m = n;
            for prime in FIRST_THOUSAND_PRIMES.iter() {
                if m == 1 {
                    break;
                }
                if m % prime == 0 {
                    primes.push(*prime);
                    while m % prime == 0 {
                        m /= prime;
                    }
                }
            }
            // This might be prohibitively expensive
            if m > 1 {
                let mut other_primes = PrimeFieldElementBig::primes_lt(m)
                    .into_iter()
                    .filter(|&x| n % x == 0)
                    .collect();
                primes.append(&mut other_primes);
            }
        };

        // N must divide the field prime minus one for a primitive nth root of unity to exist
        let one = BigInt::one();
        if !((self.q.clone() - one.clone()) % n).is_zero() {
            let primes_bigint = primes
                .iter()
                .map(|x| Into::<BigInt>::into(*x))
                .collect::<Vec<BigInt>>();
            return (None, primes_bigint);
        }

        let mut primitive_root: Option<PrimeFieldElementBig> = None;
        let mut candidate: PrimeFieldElementBig = PrimeFieldElementBig::new(one.clone(), self);
        #[allow(clippy::suspicious_operation_groupings)]
        while primitive_root == None && candidate.value < self.q {
            if (-candidate.legendre_symbol()).is_one()
                && primes.iter().filter(|&x| n % x == 0).all(|x| {
                    !candidate
                        .mod_pow_raw((self.q.clone() - one.clone()) / x)
                        .is_one()
                })
            {
                primitive_root = Some(candidate.mod_pow((self.q.clone() - 1) / n));
            }

            candidate.value += 1;
        }

        let primes_bigint = primes
            .iter()
            .map(|x| Into::<BigInt>::into(*x))
            .collect::<Vec<BigInt>>();
        (primitive_root, primes_bigint)
    }
}

#[cfg_attr(
    feature = "serialization-serde",
    derive(Serialize, Deserialize, Serializer)
)]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub struct PrimeFieldElementBig<'a> {
    pub value: BigInt,
    pub field: &'a PrimeFieldBig,
}

impl<'a> ModPowU64 for PrimeFieldElementBig<'a> {
    fn mod_pow_u64(&self, pow: u64) -> Self {
        self.mod_pow(pow.into())
    }
}

impl<'a> FieldBatchInversion for PrimeFieldElementBig<'a> {
    fn batch_inversion(&self, rhs: Vec<Self>) -> Vec<Self> {
        self.field.batch_inversion_elements(rhs)
    }
}

impl<'a> IdentityValues for PrimeFieldElementBig<'_> {
    fn ring_zero(&self) -> Self {
        Self {
            field: self.field,
            value: BigInt::zero(),
        }
    }

    fn ring_one(&self) -> Self {
        Self {
            field: self.field,
            value: BigInt::one(),
        }
    }

    fn is_zero(&self) -> bool {
        self.value == BigInt::zero()
    }

    fn is_one(&self) -> bool {
        self.value == BigInt::one()
    }
}

impl<'a> New for PrimeFieldElementBig<'_> {
    fn new_from_usize(&self, value: usize) -> Self {
        let value_bi: BigInt = Into::<BigInt>::into(value);
        Self {
            value: value_bi,
            field: self.field,
        }
    }
}

impl fmt::Display for PrimeFieldElementBig<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Pretty printing does not print the modulus value, although I guess it could...
        write!(f, "{}", self.value)
    }
}

impl<'a> PrimeFieldElementBig<'a> {
    pub fn from_bytes(field: &'a PrimeFieldBig, buf: &[u8]) -> Self {
        let value = Self::from_bytes_raw(&field.q, buf);
        Self::new(value, field)
    }

    // TODO: Is this an OK way to generate a number from a byte array?
    pub fn from_bytes_raw(modulus: &BigInt, buf: &[u8]) -> BigInt {
        let mut output_int = BigInt::zero();
        for elem in buf.iter() {
            output_int = output_int << 8 ^ Into::<BigInt>::into(*elem);
        }
        (output_int % modulus + modulus) % modulus
    }

    pub fn is_prime(n: BigInt, primes: &[BigInt]) -> bool {
        for p in primes {
            let q = n.clone() / p.to_owned();
            if q.clone() < *p {
                return true;
            };
            let r: BigInt = n.clone() - q.clone() * p.to_owned();
            if r.is_zero() {
                return false;
            };
        }
        panic!("too few primes")
    }

    // Not converted to BigInt since it is infeasible to find all primes below i128.max
    fn primes_lt(bound: i128) -> Vec<i128> {
        let mut primes: Vec<bool> = (0..bound + 1).map(|num| num == 2 || num & 1 != 0).collect();
        let mut num = 3i128;
        while num * num <= bound {
            let mut j = num * num;
            while j <= bound {
                primes[j as usize] = false;
                j += num;
            }
            num += 2;
        }
        primes
            .into_iter()
            .enumerate()
            .skip(2)
            .filter_map(|(i, p)| if p { Some(i as i128) } else { None })
            .collect::<Vec<i128>>()
    }

    pub fn new(value: BigInt, field: &'a PrimeFieldBig) -> Self {
        Self {
            value: (value % field.q.clone() + field.q.clone()) % field.q.clone(),
            field,
        }
    }

    pub fn legendre_symbol(&self) -> BigInt {
        let one = BigInt::one();
        let elem = self
            .mod_pow((self.field.q.clone() - one.clone()) / Into::<BigInt>::into(2))
            .value;

        // Ugly hack to force a result in {-1,0,1}
        if elem == self.field.q.clone() - one.clone() {
            -one
        } else {
            elem
        }
    }

    pub fn get_generator_domain(&self) -> Vec<Self> {
        let mut val = self.to_owned();
        let one = BigInt::one();
        let mut ret: Vec<Self> = vec![Self::new(one, self.field)];

        // Idiomatic way of constructing a do-while loop in Rust
        loop {
            ret.push(val.clone());
            val = val.clone() * self.to_owned();
            if val.value.is_one() {
                break;
            }
        }
        ret
    }

    fn same_field_check(&self, other: &Self, operation: &str) {
        if self.field.q != other.field.q {
            panic!(
                "Operation {} is only defined for elements in the same field. Got: q={}, p={}",
                operation, self.field.q, self.field.q
            );
        }
    }

    // Return the greatest common divisor (gcd), and factors a, b s.t. x*a + b*y = gcd(a, b).
    pub fn eea(mut x: BigInt, mut y: BigInt) -> (BigInt, BigInt, BigInt) {
        let (mut a_factor, mut a1, mut b_factor, mut b1) =
            (BigInt::one(), BigInt::zero(), BigInt::zero(), BigInt::one());

        while !y.is_zero() {
            let (quotient, remainder) = (x.clone() / y.clone(), x.clone() % y.clone());
            let (c, d) = (
                a_factor - quotient.clone() * a1.clone(),
                b_factor.clone() - quotient * b1.clone(),
            );

            x = y;
            y = remainder;
            a_factor = a1;
            a1 = c;
            b_factor = b1;
            b1 = d;
        }

        // x is the gcd
        (x, a_factor, b_factor)
    }

    pub fn inv(&self) -> Self {
        let (_, _, a) = Self::eea(self.field.q.clone(), self.value.clone());
        Self {
            field: self.field,
            value: (a % self.field.q.clone() + self.field.q.clone()) % self.field.q.clone(),
        }
    }

    pub fn mod_pow_raw(&self, pow: BigInt) -> BigInt {
        // Special case for handling 0^0 = 1
        if pow.is_zero() {
            return 1.into();
        }

        let mut acc: BigInt = BigInt::one();
        let mod_value: BigInt = self.field.q.clone();
        let res = self.value.clone();

        let bit_length: u64 = pow.bits();

        for i in 0..bit_length {
            acc = acc.clone() * acc.clone() % mod_value.clone();
            let set: bool =
                !(pow.clone() & Into::<BigInt>::into(1u128 << (bit_length - 1 - i))).is_zero();
            if set {
                acc = acc * res.clone() % mod_value.clone();
            }
        }
        acc
    }

    pub fn mod_pow(&self, pow: BigInt) -> Self {
        Self {
            value: self.mod_pow_raw(pow),
            field: self.field,
        }
    }
}

impl<'a> Add for PrimeFieldElementBig<'a> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        self.same_field_check(&other, "add");
        Self {
            value: (self.value + other.value) % self.field.q.clone(),
            field: self.field,
        }
    }
}

impl<'a> Sub for PrimeFieldElementBig<'a> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self.same_field_check(&other, "sub");
        Self {
            value: ((self.value - other.value) % self.field.q.clone() + self.field.q.clone())
                % self.field.q.clone(),
            field: self.field,
        }
    }
}

impl<'a> Mul for PrimeFieldElementBig<'a> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        self.same_field_check(&other, "mul");
        Self {
            value: self.value * other.value % self.field.q.clone(),
            field: self.field,
        }
    }
}

impl<'a> Div for PrimeFieldElementBig<'a> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        self.same_field_check(&other, "div");
        Self {
            value: other.inv().value * self.value % self.field.q.clone(),
            field: self.field,
        }
    }
}

impl<'a> Rem for PrimeFieldElementBig<'a> {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        self.same_field_check(&other, "rem");
        Self {
            value: BigInt::zero(),
            field: self.field,
        }
    }
}

impl<'a> Neg for PrimeFieldElementBig<'a> {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            value: self.field.q.clone() - self.value,
            field: self.field,
        }
    }
}

impl<'a> Add for &PrimeFieldElementBig<'a> {
    type Output = PrimeFieldElementBig<'a>;

    fn add(self, other: Self) -> PrimeFieldElementBig<'a> {
        self.same_field_check(other, "add");
        PrimeFieldElementBig {
            value: (self.value.clone() + other.value.clone()) % self.field.q.clone(),
            field: self.field,
        }
    }
}

#[cfg(test)]
mod test_modular_arithmetic_big {
    #![allow(clippy::just_underscores_and_digits)]
    use super::*;
    use crate::utils::generate_random_numbers;

    fn b(x: i128) -> BigInt {
        Into::<BigInt>::into(x)
    }

    fn bs(xs: Vec<i128>) -> Vec<BigInt> {
        xs.iter()
            .map(|x| Into::<BigInt>::into(*x))
            .collect::<Vec<BigInt>>()
    }

    #[test]
    fn batch_inversion_test_small_no_zeros() {
        let input: Vec<BigInt> = vec![b(1), b(2), b(3), b(4)];
        let field = PrimeFieldBig::new(Into::<BigInt>::into(5));
        let output = field.batch_inversion(input);
        assert_eq!(vec![b(1), b(3), b(2), b(4)], output);
    }

    #[test]
    #[should_panic]
    fn batch_inversion_test_small_with_zeros() {
        let input: Vec<BigInt> = vec![b(1), b(2), b(3), b(4), b(0)];
        let field = PrimeFieldBig::new(b(5));
        field.batch_inversion(input);
    }

    #[test]
    fn batch_inversion_test_bigger() {
        let input: Vec<BigInt> = vec![
            b(1),
            b(2),
            b(3),
            b(4),
            b(5),
            b(6),
            b(7),
            b(8),
            b(9),
            b(10),
            b(11),
            b(12),
            b(13),
            b(14),
            b(15),
            b(16),
            b(17),
            b(18),
            b(19),
            b(20),
            b(21),
            b(22),
        ];
        let field = PrimeFieldBig::new(b(23));
        let output = field.batch_inversion(input);
        assert_eq!(
            vec![
                b(1),
                b(12),
                b(8),
                b(6),
                b(14),
                b(4),
                b(10),
                b(3),
                b(18),
                b(7),
                b(21),
                b(2),
                b(16),
                b(5),
                b(20),
                b(13),
                b(19),
                b(9),
                b(17),
                b(15),
                b(11),
                b(22)
            ],
            output
        );
    }

    #[test]
    fn batch_inversion_elements_test_small() {
        let input_values: Vec<BigInt> = bs(vec![1, 2, 3, 4]);
        let field = PrimeFieldBig::new(b(5));
        let input = input_values
            .iter()
            .map(|x| PrimeFieldElementBig::new(x.to_owned(), &field))
            .collect::<Vec<PrimeFieldElementBig>>();
        let output = field.batch_inversion_elements(input);
        let output_values = output
            .iter()
            .map(|x| x.value.clone())
            .collect::<Vec<BigInt>>();
        assert_eq!(bs(vec![1, 3, 2, 4]), output_values);
    }

    #[test]
    fn sieve_of_eratosthenes() {
        // Find primes below 100
        let expected: Vec<i128> = vec![
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
            89, 97,
        ];
        let primes = PrimeFieldElementBig::primes_lt(100);
        let bi_primes = bs(primes.clone());
        for i in 0..primes.len() {
            assert_eq!(expected[i], primes[i]);
        }
        for i in 2..primes.len() {
            assert!(PrimeFieldElementBig::is_prime(
                b(expected[i]),
                &bi_primes[0..i]
            ));
        }
    }

    #[test]
    fn get_power_series_test() {
        let field = PrimeFieldBig::new(b(113));
        let power_series = field.get_power_series(b(40));
        assert_eq!(b(1), power_series.first().unwrap().to_owned());
    }

    // get_generator_domain
    #[test]
    fn get_generator_domain_test() {
        let field = PrimeFieldBig::new(b(113));
        let element = PrimeFieldElementBig::new(b(40), &field);
        let group = element.get_generator_domain();
        assert_eq!(b(1), group[0].value);
        assert_eq!(b(40), group[1].value);
        assert_eq!(b(18), group[2].value);
        assert_eq!(b(42), group[3].value);
        assert_eq!(b(42), group[3].value);
        assert_eq!(b(48), group[7].value);
    }

    #[test]
    fn roots_of_unity_big() {
        let mut field = PrimeFieldBig::new(b(17));
        for i in 2..17 {
            let (b, _) = field.get_primitive_root_of_unity(i);
            if i == 2 || i == 4 || i == 8 || i == 16 {
                assert_ne!(b, None);
            } else {
                assert_eq!(b, None);
            }
        }

        field = PrimeFieldBig::new(b(41));
        let mut count = 0;
        for i in 2..41 {
            let (b, _) = field.get_primitive_root_of_unity(i);
            match b {
                None => {}
                _ => {
                    count += 1;
                }
            }
        }
        assert_eq!(count, 7);

        field = PrimeFieldBig::new(b(761));
        let (c, _) = field.get_primitive_root_of_unity(40);
        assert_eq!(b(208), c.unwrap().value);
        let (c, _) = field.get_primitive_root_of_unity(760);
        assert_eq!(b(6), c.unwrap().value);
    }

    #[test]
    fn primitive_root_of_unity_mod_7_bigint() {
        let field = PrimeFieldBig::new(b(7));
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(2);
        assert_eq!(b(6), primitive_root.unwrap().value);
        assert_eq!(bs(vec![2]), prime_factors);
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(3);
        assert_eq!(b(2), primitive_root.unwrap().value);
        assert_eq!(bs(vec![3]), prime_factors);
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(4);
        assert_eq!(None, primitive_root);
        assert_eq!(bs(vec![2]), prime_factors);
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(5);
        assert_eq!(None, primitive_root);
        assert_eq!(bs(vec![5]), prime_factors);
    }

    // // Test vector found in https://www.vitalik.ca/general/2018/07/21/starks_part_3.html
    #[test]
    fn find_16th_root_of_unity_mod_337_bigint() {
        let field = PrimeFieldBig::new(b(337));
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(16);
        assert!(
            bs(vec![59, 146, 30, 297, 278, 191, 307, 40]).contains(&primitive_root.unwrap().value)
        );
        assert_eq!(bs(vec![2]), prime_factors);
    }

    #[test]
    fn find_40th_root_of_unity_mod_761() {
        let field = PrimeFieldBig::new(b(761));
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(40);
        assert_eq!(b(208), primitive_root.unwrap().value);
        assert_eq!(bs(vec![2, 5]), prime_factors);
    }

    #[test]
    fn primitive_root_property_based_test() {
        let primes = vec![773i128, 13367, 223, 379, 41];
        let primes_bi = bs(primes.clone());
        for i in 0..primes.len() {
            // println!("Testing prime {}", prime);
            let field = PrimeFieldBig::new(primes_bi[i].clone());
            let rands: Vec<i128> = generate_random_numbers(
                30,
                if primes[i] > 1000000 {
                    1000000
                } else {
                    primes[i]
                },
            );
            for elem in rands.iter() {
                // println!("elem = {}", *elem);
                let (root, prime_factors): (Option<PrimeFieldElementBig>, Vec<BigInt>) =
                    field.get_primitive_root_of_unity(*elem);
                assert!(prime_factors
                    .iter()
                    .all(|x| (*elem % x.to_owned()).is_zero()));
                // assert!(prime_factors
                //     .iter()
                //     .all(|&x| (elem.to_owned() % x).is_zero()));
                if *elem == 0 {
                    continue;
                }

                // verify that we can build *elem from prime_factors
                let mut m = b(*elem);
                for prime in prime_factors.clone() {
                    while (m.clone() % prime.clone()).is_zero() {
                        m = Into::<BigInt>::into(m) / prime.clone();
                    }
                }
                assert_eq!(b(1), m);

                match root {
                    None => (),
                    Some(i) => {
                        // println!(
                        //     "Found primitive root: {}^{} = 1 mod {}",
                        //     i.value, *elem, *prime
                        // );

                        // Verify that i is actually a root of unity
                        assert_eq!(b(1), i.mod_pow_raw(b(*elem)));

                        // Verify that root is actually primitive
                        for prime_factor in prime_factors.clone().iter() {
                            assert_ne!(b(1), i.mod_pow_raw(*elem / prime_factor));
                        }
                    }
                }
            }
        }
    }

    #[test]

    fn arithmetic_pointer_equals() {
        // build two prime field objects with the same modulus
        let f1 = PrimeFieldBig::new(b(101));
        let f2 = PrimeFieldBig::new(b(101));

        // build the same prime field element twice, but with pointers to the different objects
        let e1 = PrimeFieldElementBig::new(b(16), &f1);
        let e2 = PrimeFieldElementBig::new(b(16), &f2);

        // test for equality
        assert!(e1 == e2); // test passes => equality test folows all pointers to test end-values
    }

    #[test]
    fn arithmetic_bigint() {
        // Test addition, subtraction, multiplication, and division
        let _1931 = PrimeFieldBig::new(b(1931));
        let _899_1931 = PrimeFieldElementBig::new(b(899), &_1931);
        let _31_1931 = PrimeFieldElementBig::new(b(31), &_1931);
        let _1921_1931 = PrimeFieldElementBig::new(b(1921), &_1931);
        assert_eq!((_899_1931.clone() + _31_1931.clone()).value, b(930));
        assert_eq!((_899_1931.clone() + _1921_1931.clone()).value, b(889));
        assert_eq!((_899_1931.clone() - _31_1931.clone()).value, b(868));
        assert_eq!((_899_1931.clone() - _1921_1931.clone()).value, b(909));
        assert_eq!((_899_1931.clone() * _31_1931.clone()).value, b(835));
        assert_eq!((_899_1931.clone() * _1921_1931.clone()).value, b(665));
        assert_eq!((_899_1931.clone() / _31_1931.clone()).value, b(29));
        assert_eq!((_899_1931.clone() / _1921_1931.clone()).value, b(1648));

        let field_19 = PrimeFieldBig { q: b(19) };
        let field_23 = PrimeFieldBig { q: b(23) };
        let _3_19 = PrimeFieldElementBig {
            value: b(3),
            field: &field_19,
        };
        let _5_19 = PrimeFieldElementBig {
            value: b(5),
            field: &field_19,
        };
        assert_eq!(_3_19.inv(), PrimeFieldElementBig::new(b(13), &field_19));
        assert_eq!(
            PrimeFieldElementBig::new(b(13), &field_19).mul(PrimeFieldElementBig {
                value: b(5),
                field: &field_19
            }),
            PrimeFieldElementBig::new(b(8), &field_19)
        );
        assert_eq!(
            PrimeFieldElementBig::new(b(13), &field_19)
                * PrimeFieldElementBig {
                    value: b(5),
                    field: &field_19
                },
            PrimeFieldElementBig::new(b(8), &field_19)
        );
        assert_eq!(
            PrimeFieldElementBig::new(b(13), &field_19)
                + PrimeFieldElementBig {
                    value: b(5),
                    field: &field_19
                },
            PrimeFieldElementBig::new(b(18), &field_19)
        );

        assert_eq!(
            PrimeFieldElementBig::new(b(13), &field_19)
                + PrimeFieldElementBig {
                    value: b(13),
                    field: &field_19
                },
            PrimeFieldElementBig::new(b(7), &field_19)
        );
        assert_eq!(
            PrimeFieldElementBig::new(b(2), &field_23).inv(),
            PrimeFieldElementBig::new(b(12), &field_23)
        );

        // Test EAC (Extended Euclidean Algorithm/Extended Greatest Common Divider)
        let (gcd, a_factor, b_factor) = PrimeFieldElementBig::eea(b(1914), b(899));
        assert_eq!(b(8), a_factor);
        assert_eq!(b(-17), b_factor);
        assert_eq!(b(29), gcd);

        // test
        let _17 = PrimeFieldBig::new(b(17));
        let _1_17 = PrimeFieldElementBig::new(b(1), &_17);
        assert_eq!(_1_17.mod_pow(b(3)).value, b(1));
        let _1914 = PrimeFieldBig::new(b(1914));
        let _899_1914 = PrimeFieldElementBig::new(b(899), &_1914);
        assert_eq!(_899_1914.value, b(899));
        assert_eq!(_899_1914.mod_pow(b(2)).value, b(493));
        assert_eq!(_899_1914.mod_pow(b(3)).value, b(1073));
        assert_eq!(_899_1914.mod_pow(b(4)).value, b(1885));
        assert_eq!(_899_1914.mod_pow(b(5)).value, b(725));
        assert_eq!(_899_1914.mod_pow(b(6)).value, b(1015));
        assert_eq!(_899_1914.mod_pow(b(7)).value, b(1421));
        assert_eq!(_899_1914.mod_pow(b(8)).value, b(841));
        assert_eq!(_899_1914.mod_pow(b(9)).value, b(29));

        // Now with an actual prime
        assert_eq!(_899_1931.value, b(899));
        assert_eq!(_899_1931.mod_pow(b(0)).value, b(1));
        assert_eq!(_899_1931.mod_pow(b(1)).value, b(899));
        assert_eq!(_899_1931.mod_pow(b(2)).value, b(1043));
        assert_eq!(_899_1931.mod_pow(b(3)).value, b(1122));
        assert_eq!(_899_1931.mod_pow(b(4)).value, b(696));
        assert_eq!(_899_1931.mod_pow(b(5)).value, b(60));
        assert_eq!(_899_1931.mod_pow(b(6)).value, b(1803));
        assert_eq!(_899_1931.mod_pow(b(7)).value, b(788));
        assert_eq!(_899_1931.mod_pow(b(8)).value, b(1666));
        assert_eq!(_899_1931.mod_pow(b(9)).value, b(1209));
        assert_eq!(_899_1931.mod_pow(b(10)).value, b(1669));
        assert_eq!(_899_1931.mod_pow(b(11)).value, b(44));
        assert_eq!(_899_1931.mod_pow(b(12)).value, b(936));
        assert_eq!(_899_1931.mod_pow(b(13)).value, b(1479));
        assert_eq!(_899_1931.mod_pow(b(14)).value, b(1093));
        assert_eq!(_899_1931.mod_pow(b(15)).value, b(1659));
        assert_eq!(_899_1931.mod_pow(b(1930)).value, b(1)); // Fermat's Little Theorem

        // Test 0^0
        let _0_1931 = _1931.ring_zero();
        assert_eq!(_0_1931.mod_pow(b(0)).value, b(1));

        // Test the inverse function
        assert_eq!(_899_1931.inv().value, b(784));
        assert_eq!(
            _899_1931 * PrimeFieldElementBig::new(b(784), &_1931),
            PrimeFieldElementBig::new(b(1), &_1931)
        );
    }
}
