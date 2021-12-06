use crate::shared_math::traits::{IdentityValues, ModPowU64, New};
use crate::utils::{FIRST_TEN_THOUSAND_PRIMES, FIRST_THOUSAND_PRIMES};
use serde::Serialize;
use std::fmt;
use std::ops::Add;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Neg;
use std::ops::Rem;
use std::ops::Sub;

use super::traits::FieldBatchInversion;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Hash)]
pub struct PrimeField {
    pub q: i128,
}

impl PrimeField {
    pub fn new(q: i128) -> Self {
        Self { q }
    }

    pub fn ring_zero(&self) -> PrimeFieldElement {
        PrimeFieldElement {
            value: 0.into(),
            field: self,
        }
    }

    pub fn ring_one(&self) -> PrimeFieldElement {
        PrimeFieldElement {
            value: 1.into(),
            field: self,
        }
    }

    // Verify that field prime is of the form a*k + b
    // where a, b, and k are all integers
    pub fn prime_check(&self, a: i128, b: i128) -> bool {
        self.q % a == b
    }

    pub fn get_power_series(&self, root: i128) -> Vec<i128> {
        let mut val = root;
        let mut ret: Vec<i128> = vec![1];

        // Idiomatic way of constructing a do-while loop in Rust
        loop {
            ret.push(val);
            val = val * root % self.q;
            if 1 == val {
                break;
            }
        }
        ret
    }

    pub fn get_field_with_primitive_root_of_unity(
        n: i128,
        min_value: i128,
        ret: &mut Option<(Self, i128)>,
    ) {
        for prime in FIRST_TEN_THOUSAND_PRIMES.iter().filter(|&x| *x > min_value) {
            let field = PrimeField::new(*prime);
            if let (Some(i), _) = field.get_primitive_root_of_unity(n) {
                *ret = Some((PrimeField::new(*prime), i.value));
                return;
            }
        }
        *ret = None;
    }

    pub fn evaluate_straight_line(
        &self,
        (a, b): (PrimeFieldElement, PrimeFieldElement),
        x_values: &[PrimeFieldElement],
    ) -> Vec<PrimeFieldElement> {
        let values = x_values
            .iter()
            .map(|&x| (x * a + b).value)
            .collect::<Vec<i128>>();
        values
            .iter()
            .map(|x| PrimeFieldElement::new(*x, self))
            .collect::<Vec<PrimeFieldElement>>()
    }

    pub fn lagrange_interpolation_2(
        &self,
        point0: (PrimeFieldElement, PrimeFieldElement),
        point1: (PrimeFieldElement, PrimeFieldElement),
    ) -> (PrimeFieldElement, PrimeFieldElement) {
        let x_diff = point0.0 - point1.0;
        let x_diff_inv = x_diff.inv();
        let a = (point0.1 - point1.1) * x_diff_inv;
        let b = point0.1 - a * point0.0;
        (
            PrimeFieldElement::new(a.value, self),
            PrimeFieldElement::new(b.value, self),
        )
    }

    pub fn batch_inversion(&self, nums: Vec<i128>) -> Vec<i128> {
        // Adapted from https://paulmillr.com/posts/noble-secp256k1-fast-ecc/#batch-inversion
        let size = nums.len();
        if size == 0 {
            return Vec::<i128>::new();
        }

        let mut scratch: Vec<i128> = vec![0i128; size];
        let mut acc = 1i128;
        scratch[0] = nums[0];
        for i in 0..size {
            assert_ne!(nums[i], 0i128, "Cannot do batch inversion on zero");
            scratch[i] = acc;
            acc = acc * nums[i] % self.q;
        }

        // Invert the last element of the `partials` vector
        let (_, inv, _) = PrimeFieldElement::eea(acc, self.q);
        acc = inv;
        let mut res = nums;
        for i in (0..size).rev() {
            let tmp = acc * res[i] % self.q;
            res[i] = (acc * scratch[i] % self.q + self.q) % self.q;
            acc = tmp;
        }

        res
    }

    pub fn batch_inversion_elements(
        &self,
        input: Vec<PrimeFieldElement>,
    ) -> Vec<PrimeFieldElement> {
        let values = input.iter().map(|x| x.value).collect::<Vec<i128>>();
        let result_values = self.batch_inversion(values);
        result_values
            .iter()
            .map(|x| PrimeFieldElement::new(*x, self))
            .collect::<Vec<PrimeFieldElement>>()
    }

    pub fn get_primitive_root_of_unity(&self, n: i128) -> (Option<PrimeFieldElement>, Vec<i128>) {
        let mut primes: Vec<i128> = vec![];

        if n <= 1 {
            return (Some(PrimeFieldElement::new(1, self)), primes);
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
                let mut other_primes = PrimeFieldElement::primes_lt(m)
                    .into_iter()
                    .filter(|&x| n % x == 0)
                    .collect();
                primes.append(&mut other_primes);
            }
        };

        // N must divide the field prime minus one for a primitive nth root of unity to exist
        if (self.q - 1) % n != 0 {
            return (None, primes);
        }

        let mut primitive_root: Option<PrimeFieldElement> = None;
        let mut candidate: PrimeFieldElement = PrimeFieldElement::new(1, self);
        #[allow(clippy::suspicious_operation_groupings)]
        while primitive_root == None && candidate.value < self.q {
            if candidate.legendre_symbol() == -1
                && primes
                    .iter()
                    .filter(|&x| n % x == 0)
                    .all(|x| candidate.mod_pow_raw((self.q - 1) / x) != 1)
            {
                primitive_root = Some(candidate.mod_pow((self.q - 1) / n));
            }

            candidate.value += 1;
        }

        (primitive_root, primes)
    }
}

#[cfg_attr(
    feature = "serialization-serde",
    derive(Serialize, Deserialize, Serializer)
)]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy, Serialize)]
pub struct PrimeFieldElement<'a> {
    pub value: i128,
    pub field: &'a PrimeField,
}

impl<'a> ModPowU64 for PrimeFieldElement<'a> {
    fn mod_pow_u64(&self, pow: u64) -> Self {
        self.mod_pow(pow.into())
    }
}

impl<'a> FieldBatchInversion for PrimeFieldElement<'a> {
    fn batch_inversion(&self, rhs: Vec<Self>) -> Vec<Self> {
        self.field.batch_inversion_elements(rhs)
    }
}

impl<'a> IdentityValues for PrimeFieldElement<'_> {
    fn ring_zero(&self) -> Self {
        Self {
            field: self.field,
            value: 0,
        }
    }

    fn ring_one(&self) -> Self {
        Self {
            field: self.field,
            value: 1,
        }
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }

    fn is_one(&self) -> bool {
        self.value == 1
    }
}

impl<'a> New for PrimeFieldElement<'_> {
    fn new_from_usize(&self, value: usize) -> Self {
        let value_i128: i128 = value as i128;
        Self {
            value: value_i128 % self.field.q,
            field: self.field,
        }
    }
}

impl fmt::Display for PrimeFieldElement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Pretty printing does not print the modulus value, although I guess it could...
        write!(f, "{}", self.value)
    }
}

impl<'a> PrimeFieldElement<'a> {
    pub fn from_bytes(field: &'a PrimeField, buf: &[u8]) -> PrimeFieldElement<'a> {
        let value = PrimeFieldElement::from_bytes_raw(&field.q, buf);
        PrimeFieldElement::new(value, field)
    }

    // TODO: Is this an OK way to generate a number from a byte array?
    pub fn from_bytes_raw(modulus: &i128, buf: &[u8]) -> i128 {
        let mut output_int = 0i128;
        for elem in buf.iter() {
            output_int = output_int << 8 ^ *elem as i128;
        }
        (output_int % modulus + modulus) % modulus
    }

    // is_prime and primes_lt have been shamelessly stolen from
    // https://gist.github.com/glebm/440bbe2fc95e7abee40eb260ec82f85c
    pub fn is_prime(n: i128, primes: &[i128]) -> bool {
        for &p in primes {
            let q = n / p;
            if q < p {
                return true;
            };
            let r = n - q * p;
            if r == 0 {
                return false;
            };
        }
        panic!("too few primes")
    }

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

    pub fn new(value: i128, field: &'a PrimeField) -> Self {
        Self {
            value: (value % field.q + field.q) % field.q,
            field,
        }
    }

    pub fn legendre_symbol(&self) -> i128 {
        let elem = self.mod_pow((self.field.q - 1) / 2).value;

        // Ugly hack to force a result in {-1,0,1}
        if elem == self.field.q - 1 {
            -1
        } else {
            elem
        }
    }

    pub fn get_generator_domain(&self) -> Vec<PrimeFieldElement> {
        let mut val = *self;
        let mut ret: Vec<Self> = vec![PrimeFieldElement::new(1, self.field)];

        // Idiomatic way of constructing a do-while loop in Rust
        loop {
            ret.push(val);
            val = val * *self;
            if 1 == val.value {
                break;
            }
        }
        ret
    }

    fn same_field_check(&self, other: &PrimeFieldElement, operation: &str) {
        if self.field.q != other.field.q {
            panic!(
                "Operation {} is only defined for elements in the same field. Got: q={}, p={}",
                operation, self.field.q, self.field.q
            );
        }
    }

    // Return the greatest common divisor (gcd), and factors a, b s.t. x*a + b*y = gcd(a, b).
    pub fn eea<T: num_traits::Num + Clone + Copy>(mut x: T, mut y: T) -> (T, T, T) {
        let (mut a_factor, mut a1, mut b_factor, mut b1) = (
            num_traits::one(),
            num_traits::zero(),
            num_traits::zero(),
            num_traits::one(),
        );

        while y != num_traits::zero() {
            let (quotient, remainder) = (x / y, x % y);
            let (c, d) = (a_factor - quotient * a1, b_factor - quotient * b1);

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
        let (_, _, a) = Self::eea(self.field.q, self.value);
        Self {
            field: self.field,
            value: (a % self.field.q + self.field.q) % self.field.q,
        }
    }

    pub fn mod_pow_raw(&self, pow: i128) -> i128 {
        // Special case for handling 0^0 = 1
        if pow == 0 {
            return 1.into();
        }

        let mut acc: i128 = 1;
        let mod_value: i128 = self.field.q;
        let res = self.value;

        for i in 0..128 {
            acc = acc * acc % mod_value;
            let set: bool = pow & (1 << (128 - 1 - i)) != 0;
            if set {
                acc = acc * res % mod_value;
            }
        }
        acc
    }

    pub fn mod_pow(&self, pow: i128) -> Self {
        Self {
            value: self.mod_pow_raw(pow),
            field: self.field,
        }
    }
}

impl<'a> Add for PrimeFieldElement<'a> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        self.same_field_check(&other, "add");
        Self {
            value: (self.value + other.value) % self.field.q,
            field: self.field,
        }
    }
}

impl<'a> Sub for PrimeFieldElement<'a> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self.same_field_check(&other, "sub");
        Self {
            value: ((self.value - other.value) % self.field.q + self.field.q) % self.field.q,
            field: self.field,
        }
    }
}

impl<'a> Mul for PrimeFieldElement<'a> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        self.same_field_check(&other, "mul");
        Self {
            value: self.value * other.value % self.field.q,
            field: self.field,
        }
    }
}

impl<'a> Div for PrimeFieldElement<'a> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        self.same_field_check(&other, "div");
        Self {
            value: other.inv().value * self.value % self.field.q,
            field: self.field,
        }
    }
}

impl<'a> Rem for PrimeFieldElement<'a> {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        self.same_field_check(&other, "rem");
        Self {
            value: 0,
            field: self.field,
        }
    }
}

impl<'a> Neg for PrimeFieldElement<'a> {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            value: self.field.q - self.value,
            field: self.field,
        }
    }
}

// p = k*n+1 = 2^32 − 2^20 + 1 = 4293918721
// p-1=2^20*3^2*5*7*13.

#[cfg(test)]
mod test_modular_arithmetic {
    #![allow(clippy::just_underscores_and_digits)]
    use super::*;
    use crate::utils::generate_random_numbers;

    #[test]
    fn batch_inversion_test_small_no_zeros() {
        let input: Vec<i128> = vec![1, 2, 3, 4];
        let field = PrimeField::new(5);
        let output = field.batch_inversion(input);
        assert_eq!(vec![1, 3, 2, 4], output);
    }

    #[test]
    #[should_panic]
    fn batch_inversion_test_small_with_zeros() {
        let input: Vec<i128> = vec![1, 2, 3, 4, 0];
        let field = PrimeField::new(5);
        field.batch_inversion(input);
    }

    #[test]
    fn batch_inversion_test_bigger() {
        let input: Vec<i128> = vec![
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
        ];
        let field = PrimeField::new(23);
        let output = field.batch_inversion(input);
        assert_eq!(
            vec![1, 12, 8, 6, 14, 4, 10, 3, 18, 7, 21, 2, 16, 5, 20, 13, 19, 9, 17, 15, 11, 22],
            output
        );
    }

    #[test]
    fn batch_inversion_elements_test_small() {
        let input_values: Vec<i128> = vec![1, 2, 3, 4];
        let field = PrimeField::new(5);
        let input = input_values
            .iter()
            .map(|x| PrimeFieldElement::new(*x, &field))
            .collect::<Vec<PrimeFieldElement>>();
        let output = field.batch_inversion_elements(input);
        let output_values = output.iter().map(|x| x.value).collect::<Vec<i128>>();
        assert_eq!(vec![1, 3, 2, 4], output_values);
    }

    #[test]
    fn sieve_of_eratosthenes() {
        // Find primes below 100
        let expected: Vec<i128> = vec![
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
            89, 97,
        ];
        let primes = PrimeFieldElement::primes_lt(100);
        for i in 0..primes.len() {
            assert_eq!(expected[i], primes[i]);
        }
        for i in 2..primes.len() {
            assert!(PrimeFieldElement::is_prime(expected[i], &primes[0..i]));
        }
        println!("sieve successful");
    }

    #[test]
    fn get_power_series_test() {
        let field = PrimeField::new(113);
        let power_series = field.get_power_series(40);
        println!("{:?}", power_series);
    }

    // get_generator_domain
    #[test]
    fn get_generator_domain_test() {
        let field = PrimeField::new(113);
        let element = PrimeFieldElement::new(40, &field);
        let group = element.get_generator_domain();
        assert_eq!(1, group[0].value);
        assert_eq!(40, group[1].value);
        assert_eq!(18, group[2].value);
        assert_eq!(42, group[3].value);
        assert_eq!(42, group[3].value);
        assert_eq!(48, group[7].value);
    }

    #[test]
    fn roots_of_unity() {
        let mut a = PrimeField::new(17);
        for i in 2..a.q {
            let (b, _) = a.get_primitive_root_of_unity(i);
            if i == 2 || i == 4 || i == 8 || i == 16 {
                assert_ne!(b, None);
            } else {
                assert_eq!(b, None);
            }
        }

        a = PrimeField::new(41);
        let mut count = 0;
        for i in 2..a.q {
            let (b, _) = a.get_primitive_root_of_unity(i);
            match b {
                None => {}
                _ => {
                    count += 1;
                }
            }
        }
        assert_eq!(count, 7);

        a = PrimeField::new(761);
        let (b, _) = a.get_primitive_root_of_unity(40);
        assert_eq!(208, b.unwrap().value);
        let (b, _) = a.get_primitive_root_of_unity(760);
        assert_eq!(6, b.unwrap().value);
    }

    #[test]
    fn primitive_root_of_unity_mod_7() {
        let field = PrimeField::new(7);
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(2);
        assert_eq!(6, primitive_root.unwrap().value);
        assert_eq!(vec![2], prime_factors);
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(3);
        assert_eq!(2, primitive_root.unwrap().value);
        assert_eq!(vec![3], prime_factors);
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(4);
        assert_eq!(None, primitive_root);
        assert_eq!(vec![2], prime_factors);
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(5);
        assert_eq!(None, primitive_root);
        assert_eq!(vec![5], prime_factors);
    }

    // Test vector found in https://www.vitalik.ca/general/2018/07/21/starks_part_3.html
    #[test]
    fn find_16th_root_of_unity_mod_337() {
        let field = PrimeField::new(337);
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(16);
        assert!(
            vec![59i128, 146, 30, 297, 278, 191, 307, 40].contains(&primitive_root.unwrap().value)
        );
        assert_eq!(vec![2], prime_factors);
    }

    #[test]
    fn find_40th_root_of_unity_mod_761() {
        let field = PrimeField::new(761);
        let (primitive_root, prime_factors) = field.get_primitive_root_of_unity(40);
        println!("Found: {}", primitive_root.unwrap());
        assert_eq!(208, primitive_root.unwrap().value);
        assert_eq!(vec![2, 5], prime_factors);
    }

    #[test]
    fn primitive_root_property_based_test() {
        let primes = vec![773i128, 13367, 223, 379, 41];
        for prime in primes.iter() {
            // println!("Testing prime {}", prime);
            let field = PrimeField::new(*prime);
            let rands =
                generate_random_numbers(30, if *prime > 1000000 { 1000000 } else { *prime });
            for elem in rands.iter() {
                // println!("elem = {}", *elem);
                let (root, prime_factors) = field.get_primitive_root_of_unity(*elem);
                assert!(prime_factors.iter().all(|&x| *elem % x == 0));
                if *elem == 0 {
                    continue;
                }

                // verify that we can build *elem from prime_factors
                let mut m = *elem;
                for prime in prime_factors.clone() {
                    while m % prime == 0 {
                        m /= prime;
                    }
                }
                assert_eq!(1, m);

                match root {
                    None => (),
                    Some(i) => {
                        // println!(
                        //     "Found primitive root: {}^{} = 1 mod {}",
                        //     i.value, *elem, *prime
                        // );

                        // Verify that i is actually a root of unity
                        assert_eq!(1, i.mod_pow_raw(*elem));

                        // Verify that root is actually primitive
                        for prime_factor in prime_factors.clone().iter() {
                            assert_ne!(1, i.mod_pow_raw(*elem / prime_factor));
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn internal() {
        // Test addition, subtraction, multiplication, and division
        let _1931 = PrimeField::new(1931);
        let _899_1931 = PrimeFieldElement::new(899, &_1931);
        let _31_1931 = PrimeFieldElement::new(31, &_1931);
        let _1921_1931 = PrimeFieldElement::new(1921, &_1931);
        assert_eq!((_899_1931 + _31_1931).value, 930);
        assert_eq!((_899_1931 + _1921_1931).value, 889);
        assert_eq!((_899_1931 - _31_1931).value, 868);
        assert_eq!((_899_1931 - _1921_1931).value, 909);
        assert_eq!((_899_1931 * _31_1931).value, 835);
        assert_eq!((_899_1931 * _1921_1931).value, 665);
        assert_eq!((_899_1931 / _31_1931).value, 29);
        assert_eq!((_899_1931 / _1921_1931).value, 1648);

        let field_19 = PrimeField { q: 19 };
        let field_23 = PrimeField { q: 23 };
        let _3_19 = PrimeFieldElement {
            value: 3,
            field: &field_19,
        };
        let _5_19 = PrimeFieldElement {
            value: 5,
            field: &field_19,
        };
        assert_eq!(_3_19.inv(), PrimeFieldElement::new(13, &field_19));
        assert_eq!(
            PrimeFieldElement::new(13, &field_19).mul(PrimeFieldElement {
                value: 5,
                field: &field_19
            }),
            PrimeFieldElement::new(8, &field_19)
        );
        assert_eq!(
            PrimeFieldElement::new(13, &field_19)
                * PrimeFieldElement {
                    value: 5,
                    field: &field_19
                },
            PrimeFieldElement::new(8, &field_19)
        );
        assert_eq!(
            PrimeFieldElement::new(13, &field_19)
                + PrimeFieldElement {
                    value: 5,
                    field: &field_19
                },
            PrimeFieldElement::new(18, &field_19)
        );

        assert_eq!(
            PrimeFieldElement::new(13, &field_19)
                + PrimeFieldElement {
                    value: 13,
                    field: &field_19
                },
            PrimeFieldElement::new(7, &field_19)
        );
        assert_eq!(
            PrimeFieldElement::new(2, &field_23).inv(),
            PrimeFieldElement::new(12, &field_23)
        );

        // Test EAC (Extended Euclidean Algorithm/Extended Greatest Common Divider)
        let (gcd, a_factor, b_factor) = PrimeFieldElement::eea(1914, 899);
        assert_eq!(8, a_factor);
        assert_eq!(-17, b_factor);
        assert_eq!(29, gcd);

        // test
        let _17 = PrimeField::new(17);
        let _1_17 = PrimeFieldElement::new(1, &_17);
        assert_eq!(_1_17.mod_pow(3).value, 1);
        let _1914 = PrimeField::new(1914);
        let _899_1914 = PrimeFieldElement::new(899, &_1914);
        assert_eq!(_899_1914.value, 899);
        assert_eq!(_899_1914.mod_pow(2).value, 493);
        assert_eq!(_899_1914.mod_pow(3).value, 1073);
        assert_eq!(_899_1914.mod_pow(4).value, 1885);
        assert_eq!(_899_1914.mod_pow(5).value, 725);
        assert_eq!(_899_1914.mod_pow(6).value, 1015);
        assert_eq!(_899_1914.mod_pow(7).value, 1421);
        assert_eq!(_899_1914.mod_pow(8).value, 841);
        assert_eq!(_899_1914.mod_pow(9).value, 29);

        // Now with an actual prime
        assert_eq!(_899_1931.value, 899);
        assert_eq!(_899_1931.mod_pow(1).value, 899);
        assert_eq!(_899_1931.mod_pow(2).value, 1043);
        assert_eq!(_899_1931.mod_pow(3).value, 1122);
        assert_eq!(_899_1931.mod_pow(4).value, 696);
        assert_eq!(_899_1931.mod_pow(5).value, 60);
        assert_eq!(_899_1931.mod_pow(6).value, 1803);
        assert_eq!(_899_1931.mod_pow(7).value, 788);
        assert_eq!(_899_1931.mod_pow(8).value, 1666);
        assert_eq!(_899_1931.mod_pow(9).value, 1209);
        assert_eq!(_899_1931.mod_pow(10).value, 1669);
        assert_eq!(_899_1931.mod_pow(11).value, 44);
        assert_eq!(_899_1931.mod_pow(12).value, 936);
        assert_eq!(_899_1931.mod_pow(13).value, 1479);
        assert_eq!(_899_1931.mod_pow(14).value, 1093);
        assert_eq!(_899_1931.mod_pow(15).value, 1659);
        assert_eq!(_899_1931.mod_pow(1930).value, 1); // Fermat's Little Theorem

        // Test 0^0
        let _0_1931 = _1931.ring_zero();
        assert_eq!(_0_1931.mod_pow(0).value, 1);

        // Test the inverse function
        println!("{}", _899_1931.inv().value);
        assert_eq!(_899_1931.inv().value, 784);
        assert_eq!(
            _899_1931 * PrimeFieldElement::new(784, &_1931),
            PrimeFieldElement::new(1, &_1931)
        );
    }
}
