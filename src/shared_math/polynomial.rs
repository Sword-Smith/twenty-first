use crate::shared_math::ntt::{intt, ntt};
use crate::shared_math::traits::IdentityValues;
use crate::utils::has_unique_elements;
use itertools::EitherOrBoth::{Both, Left, Right};
use itertools::Itertools;
use num_bigint::BigInt;
use num_traits::Zero;
use std::convert::From;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Rem;
use std::ops::Sub;
use std::ops::{Add, Neg};

use super::traits::{FieldBatchInversion, ModPowU64, New};

fn degree_raw<T: Add + Div + Mul + Rem + Sub + IdentityValues + Display>(
    coefficients: &[T],
) -> isize {
    let mut deg = coefficients.len() as isize - 1;
    while deg >= 0 && coefficients[deg as usize].is_zero() {
        deg -= 1;
    }

    deg // -1 for the zero polynomial
}

fn pretty_print_coefficients_generic<T: Add + Div + Mul + Rem + Sub + IdentityValues + Display>(
    coefficients: &[T],
) -> String {
    let degree = degree_raw(coefficients);
    if degree == -1 {
        return String::from("0");
    }

    // for every nonzero term, in descending order
    let mut outputs: Vec<String> = Vec::new();
    let pol_degree = degree as usize;
    for i in 0..=pol_degree {
        let pow = pol_degree - i;
        if coefficients[pow].is_zero() {
            continue;
        }

        outputs.push(format!(
            "{}{}{}", // { + } { 7 } { x^3 }
            if i == 0 { "" } else { " + " },
            if coefficients[pow].is_one() {
                String::from("")
            } else {
                coefficients[pow].to_string()
            },
            if pow == 0 && coefficients[pow].is_one() {
                let one: T = coefficients[pow].ring_one();
                one.to_string()
            } else if pow == 0 {
                String::from("")
            } else if pow == 1 {
                String::from("x")
            } else {
                let mut result = "x^".to_owned();
                let borrowed_string = pow.to_string().to_owned();
                result.push_str(&borrowed_string);
                result
            }
        ));
    }
    outputs.join("")
}

#[derive(Debug, Clone)]
pub struct Polynomial<
    T: Add + Div + Mul + Rem + Sub + IdentityValues + Clone + PartialEq + Eq + Hash + Display + Debug,
> {
    pub coefficients: Vec<T>,
}

impl<
        T: Add
            + Div
            + Mul
            + Rem
            + Sub
            + IdentityValues
            + Clone
            + PartialEq
            + Eq
            + Hash
            + Display
            + Debug,
    > std::fmt::Display for Polynomial<T>
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            pretty_print_coefficients_generic(&self.coefficients)
        )
    }
}

impl<
        U: Add<Output = U>
            + Div<Output = U>
            + Mul<Output = U>
            + Rem
            + Sub<Output = U>
            + IdentityValues
            + Clone
            + PartialEq
            + Eq
            + Hash
            + Display
            + Debug,
    > PartialEq for Polynomial<U>
{
    fn eq(&self, other: &Self) -> bool {
        if self.degree() != other.degree() {
            return false;
        }

        if self.degree() == -1 {
            return true;
        }

        self.coefficients
            .iter()
            .zip(other.coefficients.iter())
            .all(|(x, y)| x == y)
    }
}

impl<
        U: Add<Output = U>
            + Div<Output = U>
            + Mul<Output = U>
            + Rem
            + Sub<Output = U>
            + IdentityValues
            + Clone
            + PartialEq
            + Eq
            + Hash
            + Display
            + Debug,
    > Eq for Polynomial<U>
{
}

impl<
        U: Add<Output = U>
            + Div<Output = U>
            + Mul<Output = U>
            + Rem
            + Sub<Output = U>
            + IdentityValues
            + Clone
            + Display
            + Debug
            + PartialEq
            + Eq
            + Hash,
    > Polynomial<U>
{
    pub fn normalize(&mut self) {
        while !self.coefficients.is_empty() && self.coefficients.last().unwrap().is_zero() {
            self.coefficients.pop();
        }
    }

    pub fn ring_zero() -> Self {
        Self {
            coefficients: vec![],
        }
    }

    pub fn from_constant(constant: U) -> Self {
        Self {
            coefficients: vec![constant],
        }
    }

    pub fn is_zero(&self) -> bool {
        self.coefficients.is_empty() || self.coefficients.iter().all(|x| x.is_zero())
    }

    pub fn is_one(&self) -> bool {
        self.degree() == 0 && self.coefficients[0].is_one()
    }

    pub fn evaluate(&self, x: &U) -> U {
        let mut acc = x.ring_zero();
        for c in self.coefficients.iter().rev() {
            acc = c.to_owned() + x.to_owned() * acc;
            // acc = c + x * &acc;
        }

        acc
    }

    // Return the polynomial which corresponds to the transformation `x -> alpha * x`
    // x should probably be called alpha below
    pub fn scale(&self, x: &U) -> Self {
        let mut acc = x.ring_one();
        let mut return_coefficients = self.coefficients.clone();
        for elem in return_coefficients.iter_mut() {
            *elem = elem.clone() * acc.clone();
            acc = acc * x.to_owned();
        }

        Self {
            coefficients: return_coefficients,
        }
    }

    pub fn lagrange_interpolation_2(point0: &(U, U), point1: &(U, U)) -> (U, U) {
        let x_diff = point0.0.clone() - point1.0.clone();
        let x_diff_inv = point0.0.ring_one() / x_diff;
        let a = (point0.1.clone() - point1.1.clone()) * x_diff_inv;
        let b = point0.1.clone() - a.clone() * point0.0.clone();

        (a, b)
    }

    pub fn are_colinear(points: &[(U, U)]) -> bool {
        if points.len() < 3 {
            println!("Too few points received. Got: {} points", points.len());
            return false;
        }

        if !has_unique_elements(points.iter().map(|p| p.0.clone())) {
            println!("Non-unique element spotted Got: {:?}", points);
            return false;
        }

        // Find 1st degree polynomial from first two points
        let one: U = points[0].0.ring_one();
        let x_diff: U = points[0].0.clone() - points[1].0.clone();
        let x_diff_inv = one / x_diff;
        let a = (points[0].1.clone() - points[1].1.clone()) * x_diff_inv;
        let b = points[0].1.clone() - a.clone() * points[0].0.clone();
        for point in points.iter().skip(2) {
            let expected = a.clone() * point.0.clone() + b.clone();
            if point.1 != expected {
                println!(
                    "L({}) = {}, expected L({}) = {}, Found: L(x) = {}x + {} from {{({},{}),({},{})}}",
                    point.0,
                    point.1,
                    point.0,
                    expected,
                    a,
                    b,
                    points[0].0,
                    points[0].1,
                    points[1].0,
                    points[1].1
                );
                return false;
            }
        }

        true
    }

    // Calculates a reversed representation of the coefficients of
    // prod_{i=0}^{N}((x- q_i))
    fn prod_helper<T: IdentityValues + Sub<Output = T> + Mul<Output = T> + Clone>(
        input: &[T],
    ) -> Vec<T> {
        if let Some((q_j, elements)) = input.split_first() {
            let one: T = q_j.ring_one();
            let zero: T = q_j.ring_zero();
            let minus_q_j = zero.clone() - q_j.to_owned();
            match elements {
                // base case is `x - q_j` := [1, -q_j]
                [] => vec![one, minus_q_j],
                _ => {
                    // The recursive call calculates (x-q_j)*rec = x*rec - q_j*rec := [0, rec] .- q_j*[rec]
                    let mut rec = Self::prod_helper(elements);
                    rec.push(zero);
                    let mut i = rec.len() - 1;
                    while i > 0 {
                        rec[i] = rec[i].clone() - q_j.to_owned() * rec[i - 1].clone();
                        i -= 1;
                    }
                    rec
                }
            }
        } else {
            panic!("Empty array received");
        }
    }

    pub fn get_polynomial_with_roots(roots: &[U]) -> Self {
        let mut coefficients = Self::prod_helper(roots);
        coefficients.reverse();
        Polynomial { coefficients }
    }

    fn slow_lagrange_interpolation_internal(xs: &[U], ys: &[U]) -> Self {
        assert_eq!(
            xs.len(),
            ys.len(),
            "x and y values must have the same length"
        );
        let roots: Vec<U> = xs.to_vec();
        let mut big_pol_coeffs = Self::prod_helper(&roots);
        big_pol_coeffs.reverse();
        let big_pol = Self {
            coefficients: big_pol_coeffs,
        };

        let zero: U = xs[0].ring_zero();
        let one: U = xs[0].ring_one();
        let mut coefficients: Vec<U> = vec![zero.clone(); xs.len()];
        for (x, y) in xs.iter().zip(ys.iter()) {
            // create a PrimeFieldPolynomial that is zero at all other points than this
            // coeffs_j = prod_{i=0, i != j}^{N}((x- q_i))
            let my_div_coefficients = vec![zero.clone() - x.clone(), one.clone()];
            let mut my_pol = Self {
                coefficients: my_div_coefficients,
            };
            my_pol = big_pol.clone() / my_pol.clone();

            let mut divisor = one.clone();
            for root in roots.iter() {
                if *root == *x {
                    continue;
                }
                divisor = divisor * (x.clone() - root.to_owned());
            }

            let mut my_coeffs: Vec<U> = my_pol.coefficients.iter().map(|x| x.to_owned()).collect();
            for coeff in my_coeffs.iter_mut() {
                *coeff = coeff.to_owned() * y.clone();
                *coeff = coeff.to_owned() / divisor.clone();
            }

            for i in 0..my_coeffs.len() {
                coefficients[i] = coefficients[i].clone() + my_coeffs[i].clone();
            }
        }

        Self { coefficients }
    }

    pub fn slow_lagrange_interpolation_new(xs: &[U], ys: &[U]) -> Self {
        if !has_unique_elements(xs.iter()) {
            panic!("Repeated x values received. Got: {:?}", xs);
        }
        if xs.len() != ys.len() {
            panic!("Attempted to interpolate with x and y values of different length");
        }

        if xs.len() == 2 {
            let (a, b) = Polynomial::lagrange_interpolation_2(
                &(xs[0].clone(), ys[0].clone()),
                &(xs[1].clone(), ys[1].clone()),
            );
            return Polynomial {
                coefficients: vec![b, a],
            };
        }

        Self::slow_lagrange_interpolation_internal(xs, ys)
    }

    // Any fast interpolation will use NTT, so this is mainly used for testing/integrity
    // purposes. This also means that it is not pivotal that this function has an optimal
    // runtime.
    pub fn slow_lagrange_interpolation(points: &[(U, U)]) -> Self {
        if !has_unique_elements(points.iter().map(|x| x.0.clone())) {
            panic!("Repeated x values received. Got: {:?}", points);
        }

        if points.len() == 2 {
            let (a, b) = Polynomial::lagrange_interpolation_2(&points[0], &points[1]);
            return Polynomial {
                coefficients: vec![b, a],
            };
        }

        let xs: Vec<U> = points.iter().map(|x| x.0.to_owned()).collect();
        let ys: Vec<U> = points.iter().map(|x| x.1.to_owned()).collect();

        Self::slow_lagrange_interpolation_internal(&xs, &ys)
    }
}

impl<
        U: Add<Output = U>
            + Div<Output = U>
            + Mul<Output = U>
            + Neg<Output = U>
            + Sized
            + New
            + Rem
            + ModPowU64
            + FieldBatchInversion
            + Sub<Output = U>
            + IdentityValues
            + Clone
            + std::fmt::Debug
            + std::fmt::Display
            + PartialEq
            + Eq
            + Hash,
    > Polynomial<U>
{
    pub fn fast_multiply(lhs: &Self, rhs: &Self, primitive_root: &U, root_order: usize) -> Self {
        assert!(
            primitive_root.mod_pow_u64(root_order as u64).is_one(),
            "provided primitive root must have the provided power."
        );
        assert!(
            !primitive_root.mod_pow_u64(root_order as u64 / 2).is_one(),
            "provided primitive root must be primitive in the right power."
        );

        if lhs.is_zero() || rhs.is_zero() {
            return Self::ring_zero();
        }

        let mut root: U = primitive_root.to_owned();
        let mut order = root_order;
        let lhs_degree = lhs.degree() as usize;
        let rhs_degree = rhs.degree() as usize;
        let degree = lhs_degree + rhs_degree;

        if degree < 8 {
            return lhs.to_owned() * rhs.to_owned();
        }

        while degree < order / 2 {
            root = root.clone() * root.clone();
            order /= 2;
        }

        let mut lhs_coefficients: Vec<U> = lhs.coefficients[0..lhs_degree + 1].to_vec();
        let mut rhs_coefficients: Vec<U> = rhs.coefficients[0..rhs_degree + 1].to_vec();
        while lhs_coefficients.len() < order {
            lhs_coefficients.push(root.ring_zero());
        }
        while rhs_coefficients.len() < order {
            rhs_coefficients.push(root.ring_zero());
        }

        let lhs_codeword: Vec<U> = ntt(&lhs_coefficients, &root);
        let rhs_codeword: Vec<U> = ntt(&rhs_coefficients, &root);

        let hadamard_product: Vec<U> = rhs_codeword
            .into_iter()
            .zip(lhs_codeword.into_iter())
            .map(|(r, l)| r * l)
            .collect();

        let mut res_coefficients = intt(&hadamard_product, &root);
        res_coefficients.truncate(degree + 1);

        Polynomial {
            coefficients: res_coefficients,
        }
    }

    // domain: polynomium roots
    pub fn fast_zerofier(domain: &[U], primitive_root: &U, root_order: usize) -> Self {
        // assert(primitive_root^root_order == primitive_root.field.one()), "supplied root does not have supplied order"
        // assert(primitive_root^(root_order//2) != primitive_root.field.one()), "supplied root is not primitive root of supplied order"

        if domain.is_empty() {
            return Self::ring_zero();
        }

        if domain.len() == 1 {
            return Self {
                coefficients: vec![-domain[0].clone(), primitive_root.ring_one()],
            };
        }

        let half = domain.len() / 2;

        let left = Self::fast_zerofier(&domain[..half], primitive_root, root_order);
        let right = Self::fast_zerofier(&domain[half..], primitive_root, root_order);
        Self::fast_multiply(&left, &right, primitive_root, root_order)
    }

    pub fn fast_evaluate(&self, domain: &[U], primitive_root: &U, root_order: usize) -> Vec<U> {
        if domain.is_empty() {
            return vec![];
        }

        if domain.len() == 1 {
            return vec![self.evaluate(&domain[0])];
        }

        let half = domain.len() / 2;

        let left_zerofier = Self::fast_zerofier(&domain[..half], primitive_root, root_order);
        let right_zerofier = Self::fast_zerofier(&domain[half..], primitive_root, root_order);

        let mut left = (self.clone() % left_zerofier).fast_evaluate(
            &domain[..half],
            primitive_root,
            root_order,
        );
        let mut right = (self.clone() % right_zerofier).fast_evaluate(
            &domain[half..],
            primitive_root,
            root_order,
        );

        left.append(&mut right);
        left
    }

    pub fn fast_interpolate(
        domain: &[U],
        values: &[U],
        primitive_root: &U,
        root_order: usize,
    ) -> Self {
        assert_eq!(
            domain.len(),
            values.len(),
            "Domain and values lengths must match"
        );
        assert!(primitive_root.mod_pow_u64(root_order as u64).is_one());

        if domain.is_empty() {
            return Self::ring_zero();
        }

        if domain.len() == 1 {
            return Polynomial {
                coefficients: vec![values[0].clone()],
            };
        }

        assert!(!primitive_root.mod_pow_u64(root_order as u64 / 2).is_one());

        let half = domain.len() / 2;
        let primitive_root_squared = primitive_root.to_owned() * primitive_root.to_owned();

        let left_zerofier =
            Self::fast_zerofier(&domain[..half], &primitive_root_squared, root_order / 2);
        let right_zerofier =
            Self::fast_zerofier(&domain[half..], &primitive_root_squared, root_order / 2);

        let left_offset: Vec<U> = Self::fast_evaluate(
            &right_zerofier,
            &domain[..half],
            &primitive_root_squared,
            root_order / 2,
        );
        let right_offset: Vec<U> = Self::fast_evaluate(
            &left_zerofier,
            &domain[half..],
            &primitive_root_squared,
            root_order / 2,
        );

        let left_targets: Vec<U> = values[..half]
            .iter()
            .zip(left_offset)
            .map(|(n, d)| n.to_owned() / d)
            .collect();
        let right_targets: Vec<U> = values[half..]
            .iter()
            .zip(right_offset)
            .map(|(n, d)| n.to_owned() / d)
            .collect();

        let left_interpolant = Self::fast_interpolate(
            &domain[..half],
            &left_targets,
            &primitive_root_squared,
            root_order / 2,
        );
        let right_interpolant = Self::fast_interpolate(
            &domain[half..],
            &right_targets,
            &primitive_root_squared,
            root_order / 2,
        );

        left_interpolant * right_zerofier + right_interpolant * left_zerofier
    }

    pub fn fast_coset_evaluate(&self, offset: &U, generator: &U, order: usize) -> Vec<U> {
        let mut coefficients = self.scale(offset).coefficients;
        coefficients.append(&mut vec![generator.ring_zero(); order - coefficients.len()]);
        ntt(&coefficients, generator)
    }

    /// Divide two polynomials under the homomorphism of evaluation for a N^2 -> N*log(N) speedup
    /// Since we often want to use this fast division for numerators and divisors that evaluate
    /// to zero in their domain, we do the division with an offset from the polynomials' original
    /// domains. The issue of zero in the numerator and divisor arises when we divide a transition
    /// polynomial with a zerofier.
    pub fn fast_coset_divide(
        lhs: &Polynomial<U>,
        rhs: &Polynomial<U>,
        offset: &U,
        primitive_root: &U,
        root_order: usize,
    ) -> Polynomial<U> {
        assert!(
            primitive_root.mod_pow_u64(root_order as u64).is_one(),
            "primitive root raised to given order must yield 1"
        );
        assert!(
            !primitive_root.mod_pow_u64(root_order as u64 / 2).is_one(),
            "primitive root raised to half of given order must not yield 1"
        );
        assert!(!rhs.is_zero(), "cannot divide by zero polynomial");

        if lhs.is_zero() {
            return Polynomial {
                coefficients: vec![],
            };
        }

        assert!(
            rhs.degree() <= lhs.degree(),
            "in polynomial division, right hand side degree must be at most that of left hand side"
        );

        let zero = lhs.coefficients[0].ring_zero();
        let mut root: U = primitive_root.to_owned();
        let mut order = root_order;
        let degree: usize = lhs.degree() as usize;

        if degree < 8 {
            return lhs.to_owned() / rhs.to_owned();
        }

        while degree < order / 2 {
            root = root.clone() * root;
            order /= 2;
        }

        let mut scaled_lhs_coefficients: Vec<U> = lhs.scale(offset).coefficients;
        scaled_lhs_coefficients.append(&mut vec![
            zero.clone();
            order - scaled_lhs_coefficients.len()
        ]);
        let mut scaled_rhs_coefficients: Vec<U> = rhs.scale(offset).coefficients;
        scaled_rhs_coefficients.append(&mut vec![
            zero.clone();
            order - scaled_rhs_coefficients.len()
        ]);

        let lhs_codeword = ntt(&scaled_lhs_coefficients, &root);
        let rhs_codeword = ntt(&scaled_rhs_coefficients, &root);

        let rhs_inverses = primitive_root.batch_inversion(rhs_codeword);
        let quotient_codeword: Vec<U> = lhs_codeword
            .iter()
            .zip(rhs_inverses)
            .map(|(l, r)| l.to_owned() * r)
            .collect();

        let scaled_quotient_coefficients = intt(&quotient_codeword, &root);

        let scaled_quotient = Polynomial {
            coefficients: scaled_quotient_coefficients,
        };

        scaled_quotient.scale(&(zero.ring_one() / offset.to_owned()))
    }
}

impl<
        U: Add<Output = U>
            + Div<Output = U>
            + Mul<Output = U>
            + Rem
            + Sub<Output = U>
            + IdentityValues
            + Clone
            + std::fmt::Debug
            + std::fmt::Display
            + PartialEq
            + Eq
            + Hash,
    > Polynomial<U>
{
    pub fn multiply(self, other: Self) -> Self {
        let degree_lhs = self.degree();
        let degree_rhs = other.degree();

        if degree_lhs < 0 || degree_rhs < 0 {
            return Self::ring_zero();
            // return self.zero();
        }

        // allocate right number of coefficients, initialized to zero
        let elem = self.coefficients[0].clone();
        let mut result_coeff: Vec<U> =
            //vec![U::zero_from_field(field: U); degree_lhs as usize + degree_rhs as usize + 1];
            vec![elem.ring_zero(); degree_lhs as usize + degree_rhs as usize + 1];

        // for all pairs of coefficients, add product to result vector in appropriate coordinate
        for i in 0..=degree_lhs as usize {
            for j in 0..=degree_rhs as usize {
                let mul: U = self.coefficients[i].clone() * other.coefficients[j].clone();
                result_coeff[i + j] = result_coeff[i + j].clone() + mul;
            }
        }

        // build and return Polynomial object
        Self {
            coefficients: result_coeff,
        }
    }

    // Multiply a polynomial with itself `pow` times
    pub fn mod_pow(&self, pow: BigInt, one: U) -> Self {
        assert!(one.is_one(), "Provided one must be one");

        // Special case to handle 0^0 = 1
        if pow.is_zero() {
            return Self::from_constant(one);
        }

        if self.is_zero() {
            return Self::ring_zero();
        }

        let one = self.coefficients.last().unwrap().ring_one();
        let mut acc = Polynomial::from_constant(one);
        let bit_length: u64 = pow.bits();
        for i in 0..bit_length {
            acc = acc.clone() * acc.clone();
            let set: bool =
                !(pow.clone() & Into::<BigInt>::into(1u128 << (bit_length - 1 - i))).is_zero();
            if set {
                acc = acc * self.clone();
            }
        }

        acc
    }

    // Multiply a polynomial with x^power
    pub fn shift_coefficients(&self, power: usize, zero: U) -> Self {
        if !zero.is_zero() {
            panic!("`zero` was not zero. Don't do this.");
        }

        let mut coefficients: Vec<U> = self.coefficients.clone();
        coefficients.splice(0..0, vec![zero; power]);
        Polynomial { coefficients }
    }

    pub fn scalar_mul(&self, scalar: U) -> Self {
        let mut coefficients: Vec<U> = vec![];
        for i in 0..self.coefficients.len() {
            coefficients.push(self.coefficients[i].clone() * scalar.clone());
        }

        Self { coefficients }
    }

    /// Return (quotient, remainder)
    pub fn divide(&self, divisor: Self) -> (Self, Self) {
        let degree_lhs = self.degree();
        let degree_rhs = divisor.degree();
        // cannot divide by zero
        if degree_rhs < 0 {
            panic!(
                "Cannot divide polynomial by zero. Got: ({:?})/({:?})",
                self, divisor
            );
        }

        // zero divided by anything gives zero. degree == -1 <=> polynomial = 0
        if self.is_zero() {
            return (Self::ring_zero(), Self::ring_zero());
        }

        // quotient is built from back to front so must be reversed
        // Preallocate space for quotient coefficients
        let mut quotient: Vec<U>;
        if degree_lhs - degree_rhs >= 0 {
            quotient = Vec::with_capacity((degree_lhs - degree_rhs + 1) as usize);
        } else {
            quotient = vec![];
        }
        let mut remainder = self.clone();
        remainder.normalize();

        let dlc: U = divisor.coefficients[degree_rhs as usize].clone(); // divisor leading coefficient
        let inv = dlc.ring_one() / dlc;

        let mut i = 0;
        while i + degree_rhs <= degree_lhs {
            // calculate next quotient coefficient, and set leading coefficient
            // of remainder remainder is 0 by removing it
            let rlc: U = remainder.coefficients.last().unwrap().to_owned();
            let q: U = rlc * inv.clone();
            quotient.push(q.clone());
            remainder.coefficients.pop();
            if q.is_zero() {
                i += 1;
                continue;
            }

            // Calculate the new remainder
            for j in 0..degree_rhs as usize {
                let rem_length = remainder.coefficients.len();
                remainder.coefficients[rem_length - j - 1] = remainder.coefficients
                    [rem_length - j - 1]
                    .clone()
                    - q.clone() * divisor.coefficients[divisor.coefficients.len() - j - 2].clone();
            }

            i += 1;
        }

        quotient.reverse();
        let quotient_pol = Self {
            coefficients: quotient,
        };

        (quotient_pol, remainder)
    }
}

impl<
        U: Add<Output = U>
            + Div<Output = U>
            + Mul<Output = U>
            + Rem
            + Sub<Output = U>
            + IdentityValues
            + Clone
            + PartialEq
            + Eq
            + Display
            + Debug
            + Hash,
    > Div for Polynomial<U>
{
    type Output = Self;

    fn div(self, other: Self) -> Self {
        let (quotient, _): (Self, Self) = self.divide(other);
        quotient
    }
}

impl<
        U: Add<Output = U>
            + Div<Output = U>
            + Mul<Output = U>
            + Rem
            + Sub<Output = U>
            + IdentityValues
            + Clone
            + PartialEq
            + Eq
            + Hash
            + Display
            + Debug,
    > Rem for Polynomial<U>
{
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        let (_, remainder): (Self, Self) = self.divide(other);
        remainder
    }
}

impl<
        U: Add<Output = U>
            + Div
            + Mul
            + Rem
            + Sub
            + IdentityValues
            + Clone
            + PartialEq
            + Eq
            + Hash
            + Display
            + Debug,
    > Add for Polynomial<U>
{
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let summed: Vec<U> = self
            .coefficients
            .iter()
            .zip_longest(other.coefficients.iter())
            .map(|a: itertools::EitherOrBoth<&U, &U>| match a {
                Both(l, r) => l.to_owned() + r.to_owned(),
                Left(l) => l.to_owned(),
                Right(r) => r.to_owned(),
            })
            .collect();

        Self {
            coefficients: summed,
        }
    }
}

impl<
        U: Add
            + Div
            + Mul
            + Rem
            + Sub<Output = U>
            + IdentityValues
            + Clone
            + PartialEq
            + Eq
            + Hash
            + Display
            + Debug,
    > Sub for Polynomial<U>
{
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let summed: Vec<U> = self
            .coefficients
            .iter()
            .zip_longest(other.coefficients.iter())
            .map(|a: itertools::EitherOrBoth<&U, &U>| match a {
                Both(l, r) => l.to_owned() - r.to_owned(),
                Left(l) => l.to_owned(),
                Right(r) => r.ring_zero() - r.to_owned(),
            })
            .collect();

        Self {
            coefficients: summed,
        }
    }
}

impl<
        U: Add
            + Div
            + Mul
            + Rem
            + Sub
            + IdentityValues
            + Clone
            + PartialEq
            + Eq
            + Hash
            + Debug
            + Display,
    > Polynomial<U>
{
    pub fn degree(&self) -> isize {
        degree_raw(&self.coefficients)
    }
}

impl<
        U: Add<Output = U>
            + Div<Output = U>
            + Mul<Output = U>
            + Rem
            + Sub<Output = U>
            + IdentityValues
            + Clone
            + std::fmt::Debug
            + std::fmt::Display
            + PartialEq
            + Eq
            + Hash,
    > Mul for Polynomial<U>
{
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Self::multiply(self, other)
    }
}

#[cfg(test)]
mod test_polynomials {
    #![allow(clippy::just_underscores_and_digits)]
    use std::vec;

    use super::super::prime_field_element::{PrimeField, PrimeFieldElement};
    use super::super::prime_field_element_big::{PrimeFieldBig, PrimeFieldElementBig};
    use super::*;
    use crate::utils::generate_random_numbers;
    use num_bigint::BigInt;

    fn b(x: i128) -> BigInt {
        Into::<BigInt>::into(x)
    }

    fn pf(value: i128, field: &PrimeField) -> PrimeFieldElement {
        PrimeFieldElement::new(value, field)
    }

    #[allow(clippy::needless_lifetimes)] // Suppress wrong warning (fails to compile without lifetime, I think)
    fn pfb<'a>(value: i128, field: &'a PrimeFieldBig) -> PrimeFieldElementBig {
        PrimeFieldElementBig::new(b(value), field)
    }

    #[test]
    fn polynomial_display_test() {
        let prime_modulus = 71;
        let _71 = PrimeFieldBig::new(b(prime_modulus));
        let empty = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![],
        };
        assert_eq!("0", empty.to_string());
        let zero = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![pfb(0, &_71)],
        };
        assert_eq!("0", zero.to_string());
        let double_zero = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![pfb(0, &_71), pfb(0, &_71)],
        };
        assert_eq!("0", double_zero.to_string());
        let one = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![pfb(1, &_71)],
        };
        assert_eq!("1", one.to_string());
        let zero_one = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![pfb(1, &_71), pfb(0, &_71)],
        };
        assert_eq!("1", zero_one.to_string());
        let zero_zero_one = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![pfb(1, &_71), pfb(0, &_71), pfb(0, &_71)],
        };
        assert_eq!("1", zero_zero_one.to_string());
        let one_zero = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![pfb(0, &_71), pfb(1, &_71)],
        };
        assert_eq!("x", one_zero.to_string());
        let one = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![pfb(1, &_71)],
        };
        assert_eq!("1", one.to_string());
        let x_plus_one = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![pfb(1, &_71), pfb(1, &_71)],
        };
        assert_eq!("x + 1", x_plus_one.to_string());
        let many_zeros = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![
                pfb(1, &_71),
                pfb(1, &_71),
                pfb(0, &_71),
                pfb(0, &_71),
                pfb(0, &_71),
            ],
        };
        assert_eq!("x + 1", many_zeros.to_string());
        let also_many_zeros = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![
                pfb(0, &_71),
                pfb(0, &_71),
                pfb(0, &_71),
                pfb(1, &_71),
                pfb(1, &_71),
            ],
        };
        assert_eq!("x^4 + x^3", also_many_zeros.to_string());
        let yet_many_zeros = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![
                pfb(1, &_71),
                pfb(0, &_71),
                pfb(0, &_71),
                pfb(0, &_71),
                pfb(1, &_71),
            ],
        };
        assert_eq!("x^4 + 1", yet_many_zeros.to_string());
    }

    #[test]
    fn polynomial_evaluate_test_big() {
        let prime_modulus = 71;
        let _71 = PrimeFieldBig::new(b(prime_modulus));
        let parabola = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![
                PrimeFieldElementBig::new(b(7), &_71),
                PrimeFieldElementBig::new(b(3), &_71),
                PrimeFieldElementBig::new(b(2), &_71),
            ],
        };
        assert_eq!(pfb(7, &_71), parabola.evaluate(&pfb(0, &_71)));
        assert_eq!(pfb(12, &_71), parabola.evaluate(&pfb(1, &_71)));
        assert_eq!(pfb(21, &_71), parabola.evaluate(&pfb(2, &_71)));
        assert_eq!(pfb(34, &_71), parabola.evaluate(&pfb(3, &_71)));
        assert_eq!(pfb(51, &_71), parabola.evaluate(&pfb(4, &_71)));
        assert_eq!(pfb(1, &_71), parabola.evaluate(&pfb(5, &_71)));
        assert_eq!(pfb(26, &_71), parabola.evaluate(&pfb(6, &_71)));
    }

    #[test]
    fn polynomial_evaluate_test() {
        let prime_modulus = 71;
        let _71 = PrimeField::new(prime_modulus);
        let parabola = Polynomial::<PrimeFieldElement> {
            coefficients: vec![
                PrimeFieldElement::new(7, &_71),
                PrimeFieldElement::new(3, &_71),
                PrimeFieldElement::new(2, &_71),
            ],
        };
        assert_eq!(
            PrimeFieldElement::new(7, &_71),
            parabola.evaluate(&PrimeFieldElement::new(0, &_71))
        );
        assert_eq!(
            PrimeFieldElement::new(12, &_71),
            parabola.evaluate(&PrimeFieldElement::new(1, &_71))
        );
        assert_eq!(
            PrimeFieldElement::new(21, &_71),
            parabola.evaluate(&PrimeFieldElement::new(2, &_71))
        );
        assert_eq!(
            PrimeFieldElement::new(34, &_71),
            parabola.evaluate(&PrimeFieldElement::new(3, &_71))
        );
        assert_eq!(
            PrimeFieldElement::new(51, &_71),
            parabola.evaluate(&PrimeFieldElement::new(4, &_71))
        );
        assert_eq!(
            PrimeFieldElement::new(1, &_71),
            parabola.evaluate(&PrimeFieldElement::new(5, &_71))
        );
        assert_eq!(
            PrimeFieldElement::new(26, &_71),
            parabola.evaluate(&PrimeFieldElement::new(6, &_71))
        );
    }

    #[test]
    fn scale_test() {
        let prime_modulus = 71;
        let _71 = PrimeField::new(prime_modulus);
        let _0_71 = PrimeFieldElement::new(0, &_71);
        let _1_71 = PrimeFieldElement::new(1, &_71);
        let _2_71 = PrimeFieldElement::new(2, &_71);
        let _3_71 = PrimeFieldElement::new(3, &_71);
        let _6_71 = PrimeFieldElement::new(6, &_71);
        let _12_71 = PrimeFieldElement::new(12, &_71);
        let _36_71 = PrimeFieldElement::new(36, &_71);
        let _37_71 = PrimeFieldElement::new(37, &_71);
        let _40_71 = PrimeFieldElement::new(40, &_71);
        let mut input = Polynomial {
            coefficients: vec![_1_71, _6_71],
        };

        let mut expected = Polynomial {
            coefficients: vec![_1_71, _12_71],
        };

        assert_eq!(expected, input.scale(&_2_71));

        input = Polynomial::ring_zero();
        expected = Polynomial::ring_zero();
        assert_eq!(expected, input.scale(&_2_71));

        input = Polynomial {
            coefficients: vec![_12_71, _12_71, _12_71, _12_71],
        };
        expected = Polynomial {
            coefficients: vec![_12_71, _36_71, _37_71, _40_71],
        };
        assert_eq!(expected, input.scale(&_3_71));
    }

    #[test]
    fn normalize_test() {
        let prime_modulus = 71;
        let _71 = PrimeField::new(prime_modulus);
        let _0_71 = PrimeFieldElement::new(0, &_71);
        let _1_71 = PrimeFieldElement::new(1, &_71);
        let _6_71 = PrimeFieldElement::new(6, &_71);
        let _12_71 = PrimeFieldElement::new(12, &_71);
        let _71 = PrimeField::new(prime_modulus);
        let zero: Polynomial<PrimeFieldElement> = Polynomial::ring_zero();
        let mut mut_one: Polynomial<PrimeFieldElement> = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_1_71],
        };
        let one: Polynomial<PrimeFieldElement> = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_1_71],
        };
        let mut a = Polynomial::<PrimeFieldElement> {
            coefficients: vec![],
        };
        a.normalize();
        assert_eq!(zero, a);
        mut_one.normalize();
        assert_eq!(one, mut_one);

        // trailing zeros are removed
        a = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_1_71, _0_71],
        };
        a.normalize();
        assert_eq!(
            Polynomial::<PrimeFieldElement> {
                coefficients: vec![_1_71],
            },
            a
        );
        a = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_1_71, _0_71, _0_71],
        };
        a.normalize();
        assert_eq!(
            Polynomial::<PrimeFieldElement> {
                coefficients: vec![_1_71],
            },
            a
        );

        // but leading zeros are not removed
        a = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_0_71, _1_71, _0_71, _0_71],
        };
        a.normalize();
        assert_eq!(
            Polynomial::<PrimeFieldElement> {
                coefficients: vec![_0_71, _1_71],
            },
            a
        );
        a = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_0_71, _1_71],
        };
        a.normalize();
        assert_eq!(
            Polynomial::<PrimeFieldElement> {
                coefficients: vec![_0_71, _1_71],
            },
            a
        );
        a = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_0_71],
        };
        a.normalize();
        assert_eq!(
            Polynomial::<PrimeFieldElement> {
                coefficients: vec![],
            },
            a
        );
    }

    #[test]
    fn get_polynomial_with_roots_test() {
        let field = PrimeField::new(31);
        assert_eq!(
            Polynomial {
                coefficients: vec![pf(30, &field), pf(0, &field), pf(1, &field)],
            },
            Polynomial::get_polynomial_with_roots(&[pf(1, &field), pf(30, &field)])
        );
        assert_eq!(
            Polynomial {
                coefficients: vec![pf(0, &field), pf(30, &field), pf(0, &field), pf(1, &field)],
            },
            Polynomial::get_polynomial_with_roots(&[pf(1, &field), pf(30, &field), pf(0, &field)])
        );
        assert_eq!(
            Polynomial {
                coefficients: vec![
                    pf(25, &field),
                    pf(11, &field),
                    pf(25, &field),
                    pf(1, &field)
                ],
            },
            Polynomial::get_polynomial_with_roots(&[pf(1, &field), pf(2, &field), pf(3, &field)])
        );
    }

    #[test]
    fn slow_lagrange_interpolation_test() {
        let field = PrimeField::new(7);

        // Verify that interpolation works with just one point
        let one_point = &[(pf(2, &field), pf(5, &field))];
        let mut interpolation_result = Polynomial::slow_lagrange_interpolation(one_point);
        println!("interpolation_result = {}", interpolation_result);
        let mut expected_result = Polynomial {
            coefficients: vec![pf(5, &field)],
        };
        assert_eq!(expected_result, interpolation_result);

        // Test with three points
        let points = &[
            (pf(0, &field), pf(6, &field)),
            (pf(1, &field), pf(6, &field)),
            (pf(2, &field), pf(2, &field)),
        ];

        interpolation_result = Polynomial::slow_lagrange_interpolation(points);
        expected_result = Polynomial {
            coefficients: vec![pf(6, &field), pf(2, &field), pf(5, &field)],
        };
        assert_eq!(expected_result, interpolation_result);

        // Use the same numbers to test evaluation
        for point in points.iter() {
            assert_eq!(point.1, interpolation_result.evaluate(&point.0));
        }

        // Test linear interpolation, when there are only two points given as input
        let two_points = &[
            (pf(0, &field), pf(6, &field)),
            (pf(2, &field), pf(2, &field)),
        ];
        interpolation_result = Polynomial::slow_lagrange_interpolation(two_points);
        expected_result = Polynomial {
            coefficients: vec![pf(6, &field), pf(5, &field)],
        };
        assert_eq!(expected_result, interpolation_result);
    }

    #[test]
    fn slow_lagrange_interpolation_test_big() {
        let field = PrimeFieldBig::new(b(7));
        let points = &[
            (pfb(0, &field), pfb(6, &field)),
            (pfb(1, &field), pfb(6, &field)),
            (pfb(2, &field), pfb(2, &field)),
        ];

        let interpolation_result = Polynomial::slow_lagrange_interpolation(points);
        let expected_result = Polynomial {
            coefficients: vec![pfb(6, &field), pfb(2, &field), pfb(5, &field)],
        };
        assert_eq!(expected_result, interpolation_result);

        // Use the same numbers to test evaluation
        for point in points.iter() {
            assert_eq!(point.1, interpolation_result.evaluate(&point.0));
        }
    }

    #[test]
    fn property_based_slow_lagrange_interpolation_test() {
        // Autogenerate a `number_of_points - 1` degree polynomial
        // We start by autogenerating the polynomial, as we would get a polynomial
        // with fractional coefficients if we autogenerated the points and derived the polynomium
        // from that.
        let field = PrimeField::new(999983i128);
        let number_of_points = 50usize;
        let coefficients: Vec<PrimeFieldElement> =
            generate_random_numbers(number_of_points, field.q)
                .iter()
                .map(|x| PrimeFieldElement::new(*x as i128, &field))
                .collect();

        let pol: Polynomial<PrimeFieldElement> = Polynomial { coefficients };

        // Evaluate polynomial in `number_of_points` points
        let points: Vec<(PrimeFieldElement, PrimeFieldElement)> = (0..number_of_points)
            .map(|x| {
                let x = PrimeFieldElement::new(x as i128, &field);
                (x, pol.evaluate(&x))
            })
            .collect();

        // Derive the `number_of_points - 1` degree polynomium from these `number_of_points` points,
        // evaluate the point values, and verify that they match the original values
        let interpolation_result: Polynomial<PrimeFieldElement> =
            Polynomial::slow_lagrange_interpolation(&points);
        assert_eq!(interpolation_result, pol);
        for point in points {
            assert_eq!(point.1, interpolation_result.evaluate(&point.0));
        }
    }

    #[test]
    fn property_based_slow_lagrange_interpolation_test_big() {
        // Autogenerate a `number_of_points - 1` degree polynomial
        // We start by autogenerating the polynomial, as we would get a polynomial
        // with fractional coefficients if we autogenerated the points and derived the polynomium
        // from that.
        let field = PrimeFieldBig::new(b(999983i128));
        let number_of_points = 50usize;
        let coefficients: Vec<PrimeFieldElementBig> =
            generate_random_numbers(number_of_points, 999983i128)
                .iter()
                .map(|x| pfb(*x as i128, &field))
                .collect();

        let pol: Polynomial<PrimeFieldElementBig> = Polynomial { coefficients };

        // Evaluate polynomial in `number_of_points` points
        let points: Vec<(PrimeFieldElementBig, PrimeFieldElementBig)> = (0..number_of_points)
            .map(|x| {
                let x = pfb(x as i128, &field);
                (x.clone(), pol.evaluate(&x))
            })
            .collect();

        // Derive the `number_of_points - 1` degree polynomium from these `number_of_points` points,
        // evaluate the point values, and verify that they match the original values
        let interpolation_result: Polynomial<PrimeFieldElementBig> =
            Polynomial::slow_lagrange_interpolation(&points);
        assert_eq!(interpolation_result, pol);
        for point in points {
            assert_eq!(point.1, interpolation_result.evaluate(&point.0));
        }
    }

    #[test]
    fn lagrange_interpolation_2_test() {
        let field = PrimeField::new(5);
        assert_eq!(
            (pf(1, &field), pf(0, &field)),
            Polynomial::lagrange_interpolation_2(
                &(pf(1, &field), pf(1, &field)),
                &(pf(2, &field), pf(2, &field))
            )
        );
        assert_eq!(
            (pf(4, &field), pf(4, &field)),
            Polynomial::lagrange_interpolation_2(
                &(pf(1, &field), pf(3, &field)),
                &(pf(2, &field), pf(2, &field))
            )
        );
        assert_eq!(
            (pf(4, &field), pf(2, &field)),
            Polynomial::lagrange_interpolation_2(
                &(pf(15, &field), pf(92, &field)),
                &(pf(19, &field), pf(108, &field))
            )
        );

        assert_eq!(
            (pf(3, &field), pf(2, &field)),
            Polynomial::lagrange_interpolation_2(
                &(pf(1, &field), pf(0, &field)),
                &(pf(2, &field), pf(3, &field))
            )
        );

        let field_big = PrimeFieldBig::new(b(5));
        assert_eq!(
            (pfb(1, &field_big), pfb(0, &field_big)),
            Polynomial::lagrange_interpolation_2(
                &(pfb(1, &field_big), pfb(1, &field_big)),
                &(pfb(2, &field_big), pfb(2, &field_big))
            )
        );
        assert_eq!(
            (pfb(4, &field_big), pfb(4, &field_big)),
            Polynomial::lagrange_interpolation_2(
                &(pfb(1, &field_big), pfb(3, &field_big)),
                &(pfb(2, &field_big), pfb(2, &field_big))
            )
        );
        assert_eq!(
            (pfb(4, &field_big), pfb(2, &field_big)),
            Polynomial::lagrange_interpolation_2(
                &(pfb(15, &field_big), pfb(92, &field_big)),
                &(pfb(19, &field_big), pfb(108, &field_big))
            )
        );
        assert_eq!(
            (pfb(3, &field_big), pfb(2, &field_big)),
            Polynomial::lagrange_interpolation_2(
                &(pfb(1, &field_big), pfb(0, &field_big)),
                &(pfb(2, &field_big), pfb(3, &field_big))
            )
        );
    }

    #[test]
    fn polynomial_are_colinear_test() {
        let field = PrimeField::new(5);
        assert!(Polynomial::are_colinear(&[
            (pf(1, &field), pf(1, &field)),
            (pf(2, &field), pf(2, &field)),
            (pf(3, &field), pf(3, &field))
        ]));
        assert!(Polynomial::are_colinear(&[
            (pf(1, &field), pf(1, &field)),
            (pf(2, &field), pf(7, &field)),
            (pf(3, &field), pf(3, &field))
        ]));
        assert!(Polynomial::are_colinear(&[
            (pf(1, &field), pf(3, &field)),
            (pf(2, &field), pf(2, &field)),
            (pf(3, &field), pf(1, &field))
        ]));
        assert!(Polynomial::are_colinear(&[
            (pf(1, &field), pf(1, &field)),
            (pf(7, &field), pf(7, &field)),
            (pf(3, &field), pf(3, &field))
        ]));
        assert!(!Polynomial::are_colinear(&[
            (pf(1, &field), pf(1, &field)),
            (pf(2, &field), pf(2, &field)),
            (pf(3, &field), pf(4, &field))
        ]));
        assert!(!Polynomial::are_colinear(&[
            (pf(1, &field), pf(1, &field)),
            (pf(2, &field), pf(3, &field)),
            (pf(3, &field), pf(3, &field))
        ]));
        assert!(!Polynomial::are_colinear(&[
            (pf(1, &field), pf(0, &field)),
            (pf(2, &field), pf(3, &field)),
            (pf(3, &field), pf(3, &field))
        ]));
        assert!(Polynomial::are_colinear(&[
            (pf(15, &field), pf(92, &field)),
            (pf(11, &field), pf(76, &field)),
            (pf(19, &field), pf(108, &field))
        ]));
        assert!(!Polynomial::are_colinear(&[
            (pf(12, &field), pf(92, &field)),
            (pf(11, &field), pf(76, &field)),
            (pf(19, &field), pf(108, &field))
        ]));

        // Disallow repeated x-values
        assert!(!Polynomial::are_colinear(&[
            (pf(12, &field), pf(92, &field)),
            (pf(11, &field), pf(76, &field)),
            (pf(11, &field), pf(108, &field))
        ]));

        // Disallow args with less than three points
        assert!(!Polynomial::are_colinear(&[
            (pf(12, &field), pf(92, &field)),
            (pf(11, &field), pf(76, &field))
        ]));
    }

    #[test]
    fn polynomial_are_colinear_test_big() {
        let field = PrimeFieldBig::new(b(5));
        assert!(Polynomial::are_colinear(&[
            (pfb(1, &field), pfb(1, &field)),
            (pfb(2, &field), pfb(2, &field)),
            (pfb(3, &field), pfb(3, &field))
        ]));
        assert!(Polynomial::are_colinear(&[
            (pfb(1, &field), pfb(1, &field)),
            (pfb(2, &field), pfb(7, &field)),
            (pfb(3, &field), pfb(3, &field))
        ]));
        assert!(Polynomial::are_colinear(&[
            (pfb(1, &field), pfb(3, &field)),
            (pfb(2, &field), pfb(2, &field)),
            (pfb(3, &field), pfb(1, &field))
        ]));
        assert!(Polynomial::are_colinear(&[
            (pfb(1, &field), pfb(1, &field)),
            (pfb(7, &field), pfb(7, &field)),
            (pfb(3, &field), pfb(3, &field))
        ]));
        assert!(!Polynomial::are_colinear(&[
            (pfb(1, &field), pfb(1, &field)),
            (pfb(2, &field), pfb(2, &field)),
            (pfb(3, &field), pfb(4, &field))
        ]));
        assert!(!Polynomial::are_colinear(&[
            (pfb(1, &field), pfb(1, &field)),
            (pfb(2, &field), pfb(3, &field)),
            (pfb(3, &field), pfb(3, &field))
        ]));
        assert!(!Polynomial::are_colinear(&[
            (pfb(1, &field), pfb(0, &field)),
            (pfb(2, &field), pfb(3, &field)),
            (pfb(3, &field), pfb(3, &field))
        ]));
        assert!(Polynomial::are_colinear(&[
            (pfb(15, &field), pfb(92, &field)),
            (pfb(11, &field), pfb(76, &field)),
            (pfb(19, &field), pfb(108, &field))
        ]));
        assert!(!Polynomial::are_colinear(&[
            (pfb(12, &field), pfb(92, &field)),
            (pfb(11, &field), pfb(76, &field)),
            (pfb(19, &field), pfb(108, &field))
        ]));

        // Disallow repeated x-values
        assert!(!Polynomial::are_colinear(&[
            (pfb(12, &field), pfb(92, &field)),
            (pfb(11, &field), pfb(76, &field)),
            (pfb(11, &field), pfb(108, &field))
        ]));

        // Disallow args with less than three points
        assert!(!Polynomial::are_colinear(&[
            (pfb(12, &field), pfb(92, &field)),
            (pfb(11, &field), pfb(76, &field))
        ]));
    }

    #[test]
    fn polynomial_shift_test() {
        let prime_modulus = 71;
        let _71 = PrimeField::new(prime_modulus);
        let pol = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(17, &_71),
                PrimeFieldElement::new(14, &_71),
            ],
        };
        assert_eq!(
            vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(17, &_71),
                PrimeFieldElement::new(14, &_71)
            ],
            pol.shift_coefficients(4, PrimeFieldElement::new(0, &_71))
                .coefficients
        );
        assert_eq!(
            vec![
                PrimeFieldElement::new(17, &_71),
                PrimeFieldElement::new(14, &_71)
            ],
            pol.shift_coefficients(0, PrimeFieldElement::new(0, &_71))
                .coefficients
        );
        assert_eq!(
            vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(17, &_71),
                PrimeFieldElement::new(14, &_71)
            ],
            pol.shift_coefficients(1, PrimeFieldElement::new(0, &_71))
                .coefficients
        );
    }

    #[test]
    fn mod_pow_test() {
        let _71 = PrimeField::new(71);
        let zero = PrimeFieldElement::new(0, &_71);
        let one = PrimeFieldElement::new(1, &_71);
        let one_pol = Polynomial::from_constant(one);

        assert_eq!(one_pol, one_pol.mod_pow(0.into(), one));
        assert_eq!(one_pol, one_pol.mod_pow(1.into(), one));
        assert_eq!(one_pol, one_pol.mod_pow(2.into(), one));
        assert_eq!(one_pol, one_pol.mod_pow(3.into(), one));

        let x = one_pol.shift_coefficients(1, zero);
        let x_squared = one_pol.shift_coefficients(2, zero);
        let x_cubed = one_pol.shift_coefficients(3, zero);
        assert_eq!(x, x.mod_pow(1.into(), one));
        assert_eq!(x_squared, x.mod_pow(2.into(), one));
        assert_eq!(x_cubed, x.mod_pow(3.into(), one));

        let pol = Polynomial {
            coefficients: vec![
                zero,
                PrimeFieldElement::new(14, &_71),
                zero,
                PrimeFieldElement::new(4, &_71),
                zero,
                PrimeFieldElement::new(8, &_71),
                zero,
                PrimeFieldElement::new(3, &_71),
            ],
        };
        let pol_squared = Polynomial {
            coefficients: vec![
                zero,
                zero,
                PrimeFieldElement::new(196, &_71),
                zero,
                PrimeFieldElement::new(112, &_71),
                zero,
                PrimeFieldElement::new(240, &_71),
                zero,
                PrimeFieldElement::new(148, &_71),
                zero,
                PrimeFieldElement::new(88, &_71),
                zero,
                PrimeFieldElement::new(48, &_71),
                zero,
                PrimeFieldElement::new(9, &_71),
            ],
        };
        let pol_cubed = Polynomial {
            coefficients: vec![
                zero,
                zero,
                zero,
                PrimeFieldElement::new(2744, &_71),
                zero,
                PrimeFieldElement::new(2352, &_71),
                zero,
                PrimeFieldElement::new(5376, &_71),
                zero,
                PrimeFieldElement::new(4516, &_71),
                zero,
                PrimeFieldElement::new(4080, &_71),
                zero,
                PrimeFieldElement::new(2928, &_71),
                zero,
                PrimeFieldElement::new(1466, &_71),
                zero,
                PrimeFieldElement::new(684, &_71),
                zero,
                PrimeFieldElement::new(216, &_71),
                zero,
                PrimeFieldElement::new(27, &_71),
            ],
        };

        assert_eq!(one_pol, pol.mod_pow(0.into(), one));
        assert_eq!(pol, pol.mod_pow(1.into(), one));
        assert_eq!(pol_squared, pol.mod_pow(2.into(), one));
        assert_eq!(pol_cubed, pol.mod_pow(3.into(), one));

        let parabola = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(5, &_71),
                PrimeFieldElement::new(41, &_71),
                PrimeFieldElement::new(19, &_71),
            ],
        };
        let parabola_squared = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(25, &_71),
                PrimeFieldElement::new(410, &_71),
                PrimeFieldElement::new(1871, &_71),
                PrimeFieldElement::new(1558, &_71),
                PrimeFieldElement::new(361, &_71),
            ],
        };
        assert_eq!(one_pol, parabola.mod_pow(0.into(), one));
        assert_eq!(parabola, parabola.mod_pow(1.into(), one));
        assert_eq!(parabola_squared, parabola.mod_pow(2.into(), one));
    }

    #[test]
    fn polynomial_arithmetic_property_based_test() {
        let prime_modulus = 71;
        let _71 = PrimeField::new(prime_modulus);
        let a_degree = 20;
        for i in 0..20 {
            let mut a = Polynomial::<PrimeFieldElement> {
                coefficients: generate_random_numbers(a_degree, prime_modulus)
                    .iter()
                    .map(|x| PrimeFieldElement::new(*x, &_71))
                    .collect(),
            };
            a.normalize();
            let mut b = Polynomial::<PrimeFieldElement> {
                coefficients: generate_random_numbers(a_degree + i, prime_modulus)
                    .iter()
                    .map(|x| PrimeFieldElement::new(*x, &_71))
                    .collect(),
            };
            b.normalize();

            let mul_a_b: Polynomial<PrimeFieldElement> = a.clone() * b.clone();
            let mul_b_a: Polynomial<PrimeFieldElement> = b.clone() * a.clone();
            let add_a_b: Polynomial<PrimeFieldElement> = a.clone() + b.clone();
            let add_b_a: Polynomial<PrimeFieldElement> = b.clone() + a.clone();
            let sub_a_b: Polynomial<PrimeFieldElement> = a.clone() - b.clone();
            let sub_b_a: Polynomial<PrimeFieldElement> = b.clone() - a.clone();

            let mut res = mul_a_b.clone() / b.clone();
            res.normalize();
            assert_eq!(res, a);
            res = mul_b_a.clone() / a.clone();
            res.normalize();
            assert_eq!(res, b);
            res = add_a_b.clone() - b.clone();
            res.normalize();
            assert_eq!(res, a);
            res = sub_a_b.clone() + b.clone();
            res.normalize();
            assert_eq!(res, a);
            res = add_b_a.clone() - a.clone();
            res.normalize();
            assert_eq!(res, b);
            res = sub_b_a.clone() + a.clone();
            res.normalize();
            assert_eq!(res, b);
            assert_eq!(add_a_b, add_b_a);
            assert_eq!(mul_a_b, mul_b_a);
            assert!(a.degree() < a_degree as isize);
            assert!(b.degree() < (a_degree + i) as isize);
            assert!(mul_a_b.degree() <= ((a_degree - 1) * 2 + i) as isize);
            assert!(add_a_b.degree() < (a_degree + i) as isize);

            let mut one = mul_a_b.clone() / mul_a_b.clone();
            assert!(one.is_one());
            one = a.clone() / a.clone();
            assert!(one.is_one());
            one = b.clone() / b.clone();
            assert!(one.is_one());
        }
    }

    #[test]
    fn polynomial_arithmetic_property_based_test_big() {
        let prime_modulus = 71;
        let _71 = PrimeFieldBig::new(b(prime_modulus));
        let a_degree = 20;
        for i in 0..20 {
            let mut a = Polynomial::<PrimeFieldElementBig> {
                coefficients: generate_random_numbers(a_degree, prime_modulus)
                    .iter()
                    .map(|x| pfb(*x, &_71))
                    .collect(),
            };
            a.normalize();
            let mut b = Polynomial::<PrimeFieldElementBig> {
                coefficients: generate_random_numbers(a_degree + i, prime_modulus)
                    .iter()
                    .map(|x| pfb(*x, &_71))
                    .collect(),
            };
            b.normalize();

            let mul_a_b: Polynomial<PrimeFieldElementBig> = a.clone() * b.clone();
            let mul_b_a: Polynomial<PrimeFieldElementBig> = b.clone() * a.clone();
            let add_a_b: Polynomial<PrimeFieldElementBig> = a.clone() + b.clone();
            let add_b_a: Polynomial<PrimeFieldElementBig> = b.clone() + a.clone();
            let sub_a_b: Polynomial<PrimeFieldElementBig> = a.clone() - b.clone();
            let sub_b_a: Polynomial<PrimeFieldElementBig> = b.clone() - a.clone();

            let mut res = mul_a_b.clone() / b.clone();
            res.normalize();
            assert_eq!(res, a);
            res = mul_b_a.clone() / a.clone();
            res.normalize();
            assert_eq!(res, b);
            res = add_a_b.clone() - b.clone();
            res.normalize();
            assert_eq!(res, a);
            res = sub_a_b.clone() + b.clone();
            res.normalize();
            assert_eq!(res, a);
            res = add_b_a.clone() - a.clone();
            res.normalize();
            assert_eq!(res, b);
            res = sub_b_a.clone() + a.clone();
            res.normalize();
            assert_eq!(res, b);
            assert_eq!(add_a_b, add_b_a);
            assert_eq!(mul_a_b, mul_b_a);
            assert!(a.degree() < a_degree as isize);
            assert!(b.degree() < (a_degree + i) as isize);
            assert!(mul_a_b.degree() <= ((a_degree - 1) * 2 + i) as isize);
            assert!(add_a_b.degree() < (a_degree + i) as isize);

            let one = mul_a_b.clone() / mul_a_b.clone();
            assert!(one.is_one());
        }
    }

    #[test]
    fn polynomial_arithmetic_division_test() {
        let _71 = PrimeField::new(71);
        let a = Polynomial::<PrimeFieldElement> {
            coefficients: vec![PrimeFieldElement::new(17, &_71)],
        };
        let b = Polynomial::<PrimeFieldElement> {
            coefficients: vec![PrimeFieldElement::new(17, &_71)],
        };
        let one = Polynomial::<PrimeFieldElement> {
            coefficients: vec![PrimeFieldElement::new(1, &_71)],
        };
        let zero = Polynomial::<PrimeFieldElement> {
            coefficients: vec![],
        };
        let zero_alt = Polynomial::<PrimeFieldElement> {
            coefficients: vec![PrimeFieldElement::new(0, &_71)],
        };
        let zero_alt_alt = Polynomial::<PrimeFieldElement> {
            coefficients: vec![PrimeFieldElement::new(0, &_71); 4],
        };
        assert_eq!(one, a / b.clone());
        let div_with_zero = zero.clone() / b.clone();
        let div_with_zero_alt = zero_alt.clone() / b.clone();
        let div_with_zero_alt_alt = zero_alt_alt.clone() / b.clone();
        assert!(div_with_zero.is_zero());
        assert!(!div_with_zero.is_one());
        assert!(div_with_zero_alt.is_zero());
        assert!(!div_with_zero_alt.is_one());
        assert!(div_with_zero_alt_alt.is_zero());
        assert!(!div_with_zero_alt_alt.is_one());
        assert!(div_with_zero.coefficients.is_empty());
        assert!(div_with_zero_alt.coefficients.is_empty());
        assert!(div_with_zero_alt_alt.coefficients.is_empty());

        let x: Polynomial<PrimeFieldElement> = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(1, &_71),
            ],
        };
        let mut prod_x = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(1, &_71),
            ],
        };
        let mut expected_quotient = Polynomial {
            coefficients: vec![PrimeFieldElement::new(1, &_71)],
        };
        assert_eq!(expected_quotient, prod_x / x.clone());
        assert_eq!(zero, zero.clone() / b);

        prod_x = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(1, &_71),
            ],
        };
        expected_quotient = Polynomial {
            coefficients: vec![PrimeFieldElement::new(1, &_71)],
        };
        assert_eq!(expected_quotient, prod_x / (x.clone() * x.clone()));

        prod_x = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(1, &_71),
                PrimeFieldElement::new(2, &_71),
            ],
        };
        expected_quotient = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(1, &_71),
                PrimeFieldElement::new(2, &_71),
            ],
        };
        assert_eq!(expected_quotient, prod_x / x.clone());

        prod_x = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(1, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(2, &_71),
            ],
        };
        expected_quotient = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(2, &_71),
            ],
        };
        assert_eq!(expected_quotient, prod_x / x.clone());

        prod_x = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(48, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(25, &_71),
                PrimeFieldElement::new(11, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(64, &_71),
                PrimeFieldElement::new(16, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(30, &_71),
            ],
        };
        expected_quotient = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(48, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(25, &_71),
                PrimeFieldElement::new(11, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(64, &_71),
                PrimeFieldElement::new(16, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(30, &_71),
            ],
        };
        assert_eq!(expected_quotient, prod_x.clone() / x.clone());

        expected_quotient = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(25, &_71),
                PrimeFieldElement::new(11, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(64, &_71),
                PrimeFieldElement::new(16, &_71),
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(30, &_71),
            ],
        };
        assert_eq!(expected_quotient, prod_x.clone() / (x.clone() * x.clone()));
        assert_eq!(
            Polynomial {
                coefficients: vec![
                    PrimeFieldElement::new(0, &_71),
                    PrimeFieldElement::new(48, &_71),
                ],
            },
            prod_x % (x.clone() * x.clone())
        );
    }

    #[test]
    fn polynomial_arithmetic_test_linear_combination() {
        let field = PrimeFieldBig::new(b(167772161));
        let tq = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![
                pfb(76432291, &field),
                pfb(6568597, &field),
                pfb(37593670, &field),
                pfb(164656139, &field),
                pfb(100728053, &field),
                pfb(8855557, &field),
                pfb(84827854, &field),
            ],
        };
        let ti = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![
                pfb(137616711, &field),
                pfb(15613095, &field),
                pfb(114041830, &field),
                pfb(68272686, &field),
            ],
        };
        let bq = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![pfb(43152288, &field), pfb(68272686, &field)],
        };
        let x_to_3 = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![
                pfb(0, &field),
                pfb(0, &field),
                pfb(0, &field),
                pfb(1, &field),
            ],
        };
        let ks = vec![
            pfb(132934501, &field),
            pfb(57662258, &field),
            pfb(76229169, &field),
            pfb(82319948, &field),
        ];
        let expected_lc = Polynomial::<PrimeFieldElementBig> {
            coefficients: vec![
                pfb(2792937, &field),
                pfb(39162406, &field),
                pfb(7217300, &field),
                pfb(58955792, &field),
                pfb(3275580, &field),
                pfb(58708383, &field),
                pfb(3119620, &field),
            ],
        };
        let linear_combination = tq
            + ti.scalar_mul(ks[0].clone())
            + (ti * x_to_3.clone()).scalar_mul(ks[1].clone())
            + bq.scalar_mul(ks[2].clone())
            + (bq * x_to_3).scalar_mul(ks[3].clone());
        assert_eq!(expected_lc, linear_combination);

        let x_values: Vec<PrimeFieldElementBig> = vec![
            pfb(1, &field),
            pfb(116878283, &field),
            pfb(71493608, &field),
            pfb(131850885, &field),
            pfb(65249968, &field),
            pfb(26998229, &field),
            pfb(30406922, &field),
            pfb(40136459, &field),
            pfb(167772160, &field),
            pfb(50893878, &field),
            pfb(96278553, &field),
            pfb(35921276, &field),
            pfb(102522193, &field),
            pfb(140773932, &field),
            pfb(137365239, &field),
            pfb(127635702, &field),
        ];
        let expected_y_values: Vec<PrimeFieldElementBig> = vec![
            pfb(5459857, &field),
            pfb(148657471, &field),
            pfb(30002611, &field),
            pfb(66137138, &field),
            pfb(8094868, &field),
            pfb(56386222, &field),
            pfb(156375138, &field),
            pfb(54481212, &field),
            pfb(27351017, &field),
            pfb(142491681, &field),
            pfb(27138843, &field),
            pfb(146662298, &field),
            pfb(151140487, &field),
            pfb(131629901, &field),
            pfb(120097158, &field),
            pfb(114758378, &field),
        ];
        for i in 0..16 {
            assert_eq!(
                expected_y_values[i],
                linear_combination.evaluate(&x_values[i])
            );
        }
    }

    #[test]
    fn fast_multiply_test() {
        let _65537 = PrimeFieldBig::new(65537.into());
        let primitive_root = _65537.get_primitive_root_of_unity(32).0.unwrap();
        println!("primitive_root = {}", primitive_root);
        let a: Polynomial<PrimeFieldElementBig> = Polynomial {
            coefficients: vec![
                pfb(1, &_65537),
                pfb(2, &_65537),
                pfb(3, &_65537),
                pfb(4, &_65537),
                pfb(5, &_65537),
                pfb(6, &_65537),
                pfb(7, &_65537),
                pfb(8, &_65537),
                pfb(9, &_65537),
                pfb(10, &_65537),
            ],
        };
        let b: Polynomial<PrimeFieldElementBig> = Polynomial {
            coefficients: vec![
                pfb(1, &_65537),
                pfb(2, &_65537),
                pfb(3, &_65537),
                pfb(4, &_65537),
                pfb(5, &_65537),
                pfb(6, &_65537),
                pfb(7, &_65537),
                pfb(8, &_65537),
                pfb(9, &_65537),
                pfb(17, &_65537),
            ],
        };
        let c_fast = Polynomial::fast_multiply(&a, &b, &primitive_root, 32);
        let c_normal = a.clone() * b.clone();
        println!("c_normal = {}", c_normal);
        println!("c_fast = {}", c_fast);
        assert_eq!(c_normal, c_fast);
        assert_eq!(
            Polynomial::ring_zero(),
            Polynomial::fast_multiply(&Polynomial::ring_zero(), &b, &primitive_root, 32)
        );
        assert_eq!(
            Polynomial::ring_zero(),
            Polynomial::fast_multiply(&a, &Polynomial::ring_zero(), &primitive_root, 32)
        );

        let one: Polynomial<PrimeFieldElementBig> = Polynomial {
            coefficients: vec![pfb(1, &_65537)],
        };
        assert_eq!(a, Polynomial::fast_multiply(&a, &one, &primitive_root, 32));
        assert_eq!(a, Polynomial::fast_multiply(&one, &a, &primitive_root, 32));
        assert_eq!(b, Polynomial::fast_multiply(&b, &one, &primitive_root, 32));
        assert_eq!(b, Polynomial::fast_multiply(&one, &b, &primitive_root, 32));
        let x: Polynomial<PrimeFieldElementBig> = Polynomial {
            coefficients: vec![pfb(0, &_65537), pfb(1, &_65537)],
        };
        assert_eq!(
            a.shift_coefficients(1, _65537.ring_zero()),
            Polynomial::fast_multiply(&x, &a, &primitive_root, 32)
        );
        assert_eq!(
            a.shift_coefficients(1, _65537.ring_zero()),
            Polynomial::fast_multiply(&a, &x, &primitive_root, 32)
        );
        assert_eq!(
            b.shift_coefficients(1, _65537.ring_zero()),
            Polynomial::fast_multiply(&x, &b, &primitive_root, 32)
        );
        assert_eq!(
            b.shift_coefficients(1, _65537.ring_zero()),
            Polynomial::fast_multiply(&b, &x, &primitive_root, 32)
        );
    }

    #[test]
    fn fast_zerofier_test() {
        let _17 = PrimeField::new(17);
        let _1_17 = PrimeFieldElement::new(1, &_17);
        let _5_17 = PrimeFieldElement::new(5, &_17);
        let _9_17 = PrimeFieldElement::new(9, &_17);
        let root_order = 8;
        let domain = vec![_1_17, _5_17];
        let actual = Polynomial::fast_zerofier(&domain, &_9_17, root_order);
        assert!(
            actual.evaluate(&_1_17).is_zero(),
            "expecting {} = 0 when x = 1",
            actual
        );
        assert!(
            actual.evaluate(&_5_17).is_zero(),
            "expecting {} = 0 when x = 5",
            actual
        );
        assert!(
            !actual.evaluate(&_9_17).is_zero(),
            "expecting {} != 0 when x = 9",
            actual
        );

        let _3_17 = PrimeFieldElement::new(3, &_17);
        let _7_17 = PrimeFieldElement::new(7, &_17);
        let _10_17 = PrimeFieldElement::new(10, &_17);
        let root_order_2 = 16;
        let domain_2 = vec![_7_17, _10_17];
        let actual_2 = Polynomial::fast_zerofier(&domain_2, &_3_17, root_order_2);
        assert!(
            actual_2.evaluate(&_7_17).is_zero(),
            "expecting {} = 0 when x = 7",
            actual_2
        );
        assert!(
            actual_2.evaluate(&_10_17).is_zero(),
            "expecting {} = 0 when x = 10",
            actual_2
        );
    }

    #[test]
    fn fast_evaluate_test() {
        let _17 = PrimeField::new(17);
        let _0_17 = _17.ring_zero();
        let _1_17 = _17.ring_one();
        let _3_17 = PrimeFieldElement::new(3, &_17);
        let _5_17 = PrimeFieldElement::new(5, &_17);

        // x^5 + x^3
        let poly = Polynomial {
            coefficients: vec![_0_17, _0_17, _0_17, _1_17, _0_17, _1_17],
        };

        let _6_17 = PrimeFieldElement::new(6, &_17);
        let _12_17 = PrimeFieldElement::new(12, &_17);
        let domain = vec![_6_17, _12_17];

        let actual = poly.fast_evaluate(&domain, &_3_17, 16);
        let expected_6 = _6_17.mod_pow(5) + _6_17.mod_pow(3);
        assert_eq!(expected_6, actual[0]);

        let expected_12 = _12_17.mod_pow(5) + _12_17.mod_pow(3);
        assert_eq!(expected_12, actual[1]);
    }

    #[test]
    fn fast_interpolate_test() {
        let _17 = PrimeField::new(17);
        let _0_17 = _17.ring_zero();
        let _1_17 = _17.ring_one();
        let _13_17 = PrimeFieldElement::new(13, &_17);
        let _5_17 = PrimeFieldElement::new(5, &_17);

        // x^3 + x^1
        let poly = Polynomial {
            coefficients: vec![_0_17, _1_17, _0_17, _1_17],
        };

        let _6_17 = PrimeFieldElement::new(6, &_17);
        let _7_17 = PrimeFieldElement::new(7, &_17);
        let _8_17 = PrimeFieldElement::new(8, &_17);
        let _9_17 = PrimeFieldElement::new(9, &_17);
        let domain = vec![_6_17, _7_17, _8_17, _9_17];

        let evals = poly.fast_evaluate(&domain, &_13_17, 4);
        let reinterp = Polynomial::fast_interpolate(&domain, &evals, &_13_17, 4);
        assert_eq!(poly, reinterp);
    }

    #[test]
    fn fast_coset_evaluate_test() {
        let _17 = PrimeField::new(17);
        let _0_17 = _17.ring_zero();
        let _1_17 = _17.ring_one();
        let _3_17 = PrimeFieldElement::new(3, &_17);
        let _9_17 = PrimeFieldElement::new(9, &_17);

        // x^5 + x^3
        let poly = Polynomial {
            coefficients: vec![_0_17, _0_17, _0_17, _1_17, _0_17, _1_17],
        };

        let values = poly.fast_coset_evaluate(&_3_17, &_9_17, 8);

        let mut domain = vec![_0_17; 8];
        domain[0] = _3_17.clone();
        for i in 1..8 {
            domain[i] = domain[i - 1].to_owned() * _9_17.to_owned();
        }

        let reinterp = Polynomial::fast_interpolate(&domain, &values, &_9_17, 8);
        assert_eq!(reinterp, poly);
    }

    #[test]
    fn fast_coset_divide_test() {
        let _65537 = PrimeFieldBig::new(65537.into());
        let offset = _65537.get_primitive_root_of_unity(64).0.unwrap();
        let primitive_root = _65537.get_primitive_root_of_unity(32).0.unwrap();
        println!("primitive_root = {}", primitive_root);
        let a: Polynomial<PrimeFieldElementBig> = Polynomial {
            coefficients: vec![
                pfb(1, &_65537),
                pfb(2, &_65537),
                pfb(3, &_65537),
                pfb(4, &_65537),
                pfb(5, &_65537),
                pfb(6, &_65537),
                pfb(7, &_65537),
                pfb(8, &_65537),
                pfb(9, &_65537),
                pfb(10, &_65537),
            ],
        };
        let b: Polynomial<PrimeFieldElementBig> = Polynomial {
            coefficients: vec![
                pfb(1, &_65537),
                pfb(2, &_65537),
                pfb(3, &_65537),
                pfb(4, &_65537),
                pfb(5, &_65537),
                pfb(6, &_65537),
                pfb(7, &_65537),
                pfb(8, &_65537),
                pfb(9, &_65537),
                pfb(17, &_65537),
            ],
        };
        let c_fast = Polynomial::fast_multiply(&a, &b, &primitive_root, 32);

        let mut quotient = Polynomial::fast_coset_divide(&c_fast, &b, &offset, &primitive_root, 32);
        assert_eq!(a, quotient);

        quotient = Polynomial::fast_coset_divide(&c_fast, &a, &offset, &primitive_root, 32);
        assert_eq!(b, quotient);
    }

    #[test]
    fn polynomial_arithmetic_test() {
        let _71 = PrimeField::new(71);
        let _6_71 = PrimeFieldElement::new(6, &_71);
        let _12_71 = PrimeFieldElement::new(12, &_71);
        let _16_71 = PrimeFieldElement::new(16, &_71);
        let _17_71 = PrimeFieldElement::new(17, &_71);
        let _22_71 = PrimeFieldElement::new(22, &_71);
        let _28_71 = PrimeFieldElement::new(28, &_71);
        let _33_71 = PrimeFieldElement::new(33, &_71);
        let _38_71 = PrimeFieldElement::new(38, &_71);
        let _49_71 = PrimeFieldElement::new(49, &_71);
        let _60_71 = PrimeFieldElement::new(60, &_71);
        let _64_71 = PrimeFieldElement::new(64, &_71);
        let _65_71 = PrimeFieldElement::new(65, &_71);
        let _66_71 = PrimeFieldElement::new(66, &_71);
        let mut a = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_17_71],
        };
        let mut b = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_16_71],
        };
        let mut sum = a + b;
        let mut expected_sum = Polynomial {
            coefficients: vec![_33_71],
        };
        assert_eq!(expected_sum, sum);

        // Verify overflow handling
        a = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_66_71],
        };
        b = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_65_71],
        };
        sum = a + b;
        expected_sum = Polynomial {
            coefficients: vec![_60_71],
        };
        assert_eq!(expected_sum, sum);

        // Verify handling of multiple indices
        a = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_66_71, _66_71, _66_71],
        };
        b = Polynomial::<PrimeFieldElement> {
            coefficients: vec![_33_71, _33_71, _17_71, _65_71],
        };
        sum = a.clone() + b.clone();
        expected_sum = Polynomial {
            coefficients: vec![_28_71, _28_71, _12_71, _65_71],
        };
        assert_eq!(expected_sum, sum);

        let mut diff = a.clone() - b.clone();
        let mut expected_diff = Polynomial {
            coefficients: vec![_33_71, _33_71, _49_71, _6_71],
        };
        assert_eq!(expected_diff, diff);

        diff = b.clone() - a.clone();
        expected_diff = Polynomial {
            coefficients: vec![_38_71, _38_71, _22_71, _65_71],
        };
        assert_eq!(expected_diff, diff);

        // Test multiplication
        let mut prod = a.clone() * b.clone();
        let mut expected_prod = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(48, &_71),
                PrimeFieldElement::new(25, &_71),
                PrimeFieldElement::new(11, &_71),
                PrimeFieldElement::new(64, &_71),
                PrimeFieldElement::new(16, &_71),
                PrimeFieldElement::new(30, &_71),
            ],
        };
        assert_eq!(expected_prod, prod);
        assert_eq!(5, prod.degree());
        assert_eq!(2, a.degree());
        assert_eq!(3, b.degree());

        let zero: Polynomial<PrimeFieldElement> = Polynomial {
            coefficients: vec![],
        };
        let zero_alt: Polynomial<PrimeFieldElement> = Polynomial::ring_zero();
        assert_eq!(zero, zero_alt);
        let one: Polynomial<PrimeFieldElement> = Polynomial {
            coefficients: vec![PrimeFieldElement::new(1, &_71)],
        };
        // let five: Polynomial<PrimeFieldElement> = Polynomial {
        //     coefficients: vec![PrimeFieldElement::new(5, &_71)],
        // };
        let x: Polynomial<PrimeFieldElement> = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(1, &_71),
            ],
        };
        assert_eq!(-1, zero.degree());
        assert_eq!(0, one.degree());
        assert_eq!(1, x.degree());
        assert_eq!(zero, prod.clone() * zero.clone());
        assert_eq!(prod, prod.clone() * one.clone());
        assert_eq!(x, x.clone() * one.clone());

        assert_eq!("0", zero.to_string());
        assert_eq!("1", one.to_string());
        assert_eq!("x", x.to_string());
        assert_eq!("66x^2 + 66x + 66", a.to_string());

        expected_prod = Polynomial {
            coefficients: vec![
                PrimeFieldElement::new(0, &_71),
                PrimeFieldElement::new(48, &_71),
                PrimeFieldElement::new(25, &_71),
                PrimeFieldElement::new(11, &_71),
                PrimeFieldElement::new(64, &_71),
                PrimeFieldElement::new(16, &_71),
                PrimeFieldElement::new(30, &_71),
            ],
        };
        prod = prod.clone() * x.clone();
        assert_eq!(expected_prod, prod);
        assert_eq!(
            "30x^6 + 16x^5 + 64x^4 + 11x^3 + 25x^2 + 48x",
            prod.to_string()
        );
    }
}
