use crate::shared_math::low_degree_test;
use crate::shared_math::low_degree_test::LowDegreeProof;
use crate::shared_math::ntt::{intt, ntt};
use crate::shared_math::polynomial::Polynomial;
use crate::shared_math::prime_field_element::PrimeFieldElement;
use crate::shared_math::prime_field_element_big::{PrimeFieldBig, PrimeFieldElementBig};
use crate::shared_math::traits::{IdentityValues, New};
use crate::util_types::merkle_tree::{CompressedAuthenticationPath, MerkleTree};
use crate::utils;
use num_bigint::BigInt;
use serde::de::DeserializeOwned;
use serde::Serialize;
use std::error::Error;
use std::fmt;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::Add;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Neg;
use std::ops::Rem;
use std::ops::Sub;

#[derive(Debug, PartialEq, Eq)]
pub enum StarkProofError {
    InputOutputMismatch,
    HighDegreeExtendedComputationalTrace,
    HighDegreeBoundaryQuotient,
    HighDegreeTransitionQuotient,
    HighDegreeLinearCombination,
    NonZeroBoundaryRemainder,
    NonZeroTransitionRemainder,
}

impl Error for StarkProofError {}

impl fmt::Display for StarkProofError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum StarkVerifyError {
    BadAirPaths,
    BadNextAirPaths,
    BadAirBoundaryIndentity(usize),
    BadAirTransitionIdentity(usize),
    BadBoundaryConditionPaths,
    LinearCombinationAuthenticationPath,
    LinearCombinationTupleMismatch(usize), // integer refers to first index where a mismatch is found
    InputOutputMismatch,
    HighDegreeExtendedComputationalTrace,
    HighDegreeBoundaryQuotient,
    HighDegreeTransitionQuotient,
    HighDegreeLinearCombination,
    NonZeroBoundaryRemainder,
    NonZeroTransitionRemainder,
}

impl Error for StarkVerifyError {}

impl fmt::Display for StarkVerifyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Clone, Debug, Serialize, PartialEq)]
pub struct StarkProof<T: Clone + Debug + Serialize + PartialEq> {
    tuple_merkle_root: [u8; 32],
    linear_combination_merkle_root: [u8; 32],
    air_tuple_authentication_paths: Vec<CompressedAuthenticationPath<(T, T, T)>>,
    next_air_tuple_authentication_paths: Vec<CompressedAuthenticationPath<(T, T, T)>>,
    // TODO: Change this to three Merkle trees instead, do not store all triplets in a single
    // Merkle tree!
    bc_tuple_authentication_paths: Vec<CompressedAuthenticationPath<(T, T, T)>>,
    lc_tuple_authentication_paths: Vec<CompressedAuthenticationPath<(T, T, T)>>,
    linear_combination_fri: LowDegreeProof<T>,
    index_picker_preimage: Vec<u8>,
}

#[derive(Clone, Debug, Serialize)]
pub struct MimcClaim<T: Clone + Debug + Serialize + PartialEq> {
    input: T,
    output: T,
    round_constants: Vec<T>,
}

// Returns a pair of polynomials, the numerator and denominator of the zerofier polynomias
fn get_transition_zerofier_polynomials<
    T: Clone
        + Debug
        + Serialize
        + Mul<Output = T>
        + Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + Neg<Output = T>
        + IdentityValues
        + PartialEq
        + Eq
        + Hash
        + Display,
>(
    num_steps: usize,
    last_x_value_of_trace: &T,
) -> (Polynomial<T>, Polynomial<T>) {
    let mut transition_zerofier_numerator_coefficients =
        vec![last_x_value_of_trace.ring_zero(); num_steps + 2];
    transition_zerofier_numerator_coefficients[0] = -last_x_value_of_trace.ring_one();
    transition_zerofier_numerator_coefficients[num_steps + 1] = last_x_value_of_trace.ring_one();
    let transition_zerofier_numerator = Polynomial {
        coefficients: transition_zerofier_numerator_coefficients,
    };
    let transition_zerofier_denominator_coefficients = vec![
        -last_x_value_of_trace.clone(),
        last_x_value_of_trace.ring_one(),
    ];
    let transition_zerofier_denominator = Polynomial {
        coefficients: transition_zerofier_denominator_coefficients,
    };
    (
        transition_zerofier_numerator,
        transition_zerofier_denominator,
    )
}

fn get_extended_computational_trace<
    T: Clone
        + Debug
        + Serialize
        + Mul<Output = T>
        + Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + Neg<Output = T>
        + IdentityValues
        + New
        + PartialEq
        + Eq
        + Hash
        + Display,
>(
    omega: &T,
    omicron: &T,
    num_steps: usize,
    expansion_factor: usize,
    computational_trace: &[T],
) -> (Vec<T>, Polynomial<T>) {
    let trace_interpolant_coefficients = intt(&computational_trace, &omicron);
    let trace_interpolant = Polynomial {
        coefficients: trace_interpolant_coefficients.clone(),
    };
    let mut padded_trace_interpolant_coefficients = trace_interpolant_coefficients;
    padded_trace_interpolant_coefficients.append(&mut vec![
        omega.ring_zero();
        (expansion_factor - 1) * (num_steps + 1)
    ]);
    (
        ntt(&padded_trace_interpolant_coefficients, &omega),
        trace_interpolant,
    )
}

fn get_round_constants_coefficients<
    T: Clone
        + Debug
        + Serialize
        + Mul<Output = T>
        + Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + Neg<Output = T>
        + IdentityValues
        + New
        + PartialEq
        + Eq
        + Hash
        + Display,
>(
    omicron: &T,
    mimc_round_constants: &[T],
) -> Vec<T> {
    let mut mimc_round_constants_padded = mimc_round_constants.to_vec();
    mimc_round_constants_padded.append(&mut vec![omicron.ring_zero()]);
    intt(&mimc_round_constants_padded, &omicron)
}

fn get_extended_round_constant<
    T: Clone
        + Debug
        + Serialize
        + Mul<Output = T>
        + Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + Neg<Output = T>
        + IdentityValues
        + New
        + PartialEq
        + Eq
        + Hash
        + Display,
>(
    omega: &T,
    omicron: &T,
    num_steps: usize,
    expansion_factor: usize,
    mimc_round_constants: &[T],
) -> Vec<T> {
    let mut padded_round_constants_interpolant =
        get_round_constants_coefficients(omicron, mimc_round_constants);
    padded_round_constants_interpolant.append(&mut vec![
        omega.ring_zero();
        (expansion_factor - 1) * (num_steps + 1)
    ]);

    ntt(&padded_round_constants_interpolant, &omega)
}

fn get_boundary_zerofier_polynomial<
    T: Clone
        + Debug
        + Serialize
        + Mul<Output = T>
        + Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + Neg<Output = T>
        + IdentityValues
        + PartialEq
        + Eq
        + Hash
        + Display,
>(
    last_x_value_of_trace: &T,
) -> Polynomial<T> {
    Polynomial {
        coefficients: vec![
            last_x_value_of_trace.clone(),
            -last_x_value_of_trace.clone() - last_x_value_of_trace.ring_one(),
            last_x_value_of_trace.ring_one(),
        ],
    }
}

fn get_boundary_constraint_polynomial<
    T: Clone
        + Debug
        + Serialize
        + Mul<Output = T>
        + Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + Neg<Output = T>
        + IdentityValues
        + PartialEq
        + Eq
        + Hash
        + Display,
>(
    mimc_input: &T,
    mimc_output: &T,
    last_x_value_of_trace: &T,
) -> Polynomial<T> {
    let (line_a, line_b): (T, T) = Polynomial::lagrange_interpolation_2(
        &(mimc_input.ring_one(), mimc_input.clone()),
        &(last_x_value_of_trace.to_owned(), mimc_output.to_owned()),
    );
    Polynomial {
        coefficients: vec![line_b, line_a],
    }
}

fn get_linear_combination_coefficients<'a>(
    field: &'a PrimeFieldBig,
    root_hash: &[u8; 32],
) -> Vec<PrimeFieldElementBig<'a>> {
    let k_seeds = utils::get_n_hash_rounds(root_hash, 5);
    k_seeds
        .iter()
        .map(|seed| PrimeFieldElementBig::from_bytes(field, seed))
        .collect::<Vec<PrimeFieldElementBig>>()
}

struct PolynomialEvaluations<T: Clone + Debug + Serialize + PartialEq> {
    extended_computational_trace: T,
    shifted_trace_codeword: T,
    transition_quotient_codeword: T,
    shifted_transition_quotient_codeword: T,
    boundary_quotient_codeword: T,
    shifted_boundary_quotient_codeword: T,
}

fn get_linear_combination<
    T: Clone + Debug + Serialize + PartialEq + Mul<Output = T> + Add<Output = T>,
>(
    coefficients: &[T],
    values: PolynomialEvaluations<T>,
) -> T {
    values.extended_computational_trace.clone()
        + coefficients[0].clone() * values.shifted_trace_codeword
        + coefficients[1].clone() * values.transition_quotient_codeword
        + coefficients[2].clone() * values.shifted_transition_quotient_codeword
        + coefficients[3].clone() * values.boundary_quotient_codeword
        + coefficients[4].clone() * values.shifted_boundary_quotient_codeword
}

fn get_linear_combinations<
    T: Clone + Debug + Serialize + PartialEq + Mul<Output = T> + Add<Output = T>,
>(
    coefficients: &[T],
    values: Vec<PolynomialEvaluations<T>>,
) -> Vec<T> {
    values
        .into_iter()
        .map(|value| get_linear_combination(coefficients, value))
        .collect::<Vec<T>>()
}

pub fn mimc_forward<'a>(
    input: &'a PrimeFieldElementBig,
    num_steps: usize,
    round_costants: &'a [PrimeFieldElementBig],
) -> Vec<PrimeFieldElementBig<'a>> {
    let mut computational_trace: Vec<PrimeFieldElementBig> = Vec::with_capacity(num_steps);
    let mut res: PrimeFieldElementBig = input.to_owned();
    computational_trace.push(input.to_owned());
    for i in 0..num_steps {
        res = res.clone().mod_pow(Into::<BigInt>::into(3))
            + round_costants[i % round_costants.len()].clone();
        computational_trace.push(res.clone());
    }

    computational_trace
}

pub fn mimc_forward_i128<'a>(
    input: &'a PrimeFieldElement,
    steps: usize,
    round_costants: &'a [PrimeFieldElement],
) -> Vec<PrimeFieldElement<'a>> {
    let mut computational_trace: Vec<PrimeFieldElement<'a>> = Vec::with_capacity(steps);
    let mut res: PrimeFieldElement<'a> = *input;
    computational_trace.push(*input);
    for i in 0..steps {
        res = res.mod_pow(3) + round_costants[i % round_costants.len()];
        computational_trace.push(res);
    }

    computational_trace
}

pub fn mimc_backward<'a>(
    input: &'a PrimeFieldElement,
    steps: usize,
    round_costants: &'a [PrimeFieldElement],
) -> PrimeFieldElement<'a> {
    // Verify that field.q is of the form 6k + 5
    if !input.field.prime_check(6, 5) {
        panic!("Invalid prime field selected");
    }

    let rc_length = round_costants.len() as i64;
    let start_index = steps as i64 % round_costants.len() as i64 - 1;
    let mut res: PrimeFieldElement<'a> = *input;
    for i in 0..steps as i64 {
        let index = (((start_index - i % rc_length) + rc_length) % rc_length) as usize;
        res = (res - round_costants[index]).mod_pow((2 * (input.field.q) - 1) / 3);
    }

    res
}

impl<U: Clone + Debug + Display + DeserializeOwned + PartialEq + Serialize> StarkProof<U> {
    pub fn from_serialization(
        transcript: Vec<u8>,
        start_index: usize,
    ) -> Result<(StarkProof<U>, usize), Box<dyn Error>> {
        // tuple Merkle root is first 32 bytes
        let mut index = start_index;
        let tuple_merkle_root: [u8; 32] = bincode::deserialize(&transcript[index..index + 32])?;
        index += 32;
        let (linear_combination_fri, new_index) =
            LowDegreeProof::<U>::from_serialization(transcript.clone(), index)?;
        index = new_index;
        let index_picker_preimage: Vec<u8> = transcript[0..index].to_vec();
        let linear_combination_merkle_root: [u8; 32] =
            bincode::deserialize(&transcript[index..index + 32])?;
        index += 32;

        // Get LC tuple authentication paths
        let mut proof_size: u32 = bincode::deserialize(&transcript[index..index + 4])?;
        index += 4;
        let lc_tuple_authentication_paths: Vec<CompressedAuthenticationPath<(U, U, U)>> =
            bincode::deserialize_from(&transcript[index..index + proof_size as usize])?;
        index += proof_size as usize;

        // Get Next AIR tuple authentication paths
        proof_size = bincode::deserialize(&transcript[index..index + 4])?;
        index += 4;
        let next_air_tuple_authentication_paths: Vec<CompressedAuthenticationPath<(U, U, U)>> =
            bincode::deserialize_from(&transcript[index..index + proof_size as usize])?;
        index += proof_size as usize;

        // Get AIR tuple authentication paths
        proof_size = bincode::deserialize(&transcript[index..index + 4])?;
        index += 4;
        let air_tuple_authentication_paths: Vec<CompressedAuthenticationPath<(U, U, U)>> =
            bincode::deserialize_from(&transcript[index..index + proof_size as usize])?;
        index += proof_size as usize;

        // Get AIR boundary authentication paths
        proof_size = bincode::deserialize(&transcript[index..index + 4])?;
        index += 4;
        let bc_tuple_authentication_paths: Vec<CompressedAuthenticationPath<(U, U, U)>> =
            bincode::deserialize_from(&transcript[index..index + proof_size as usize])?;
        index += proof_size as usize;

        Ok((
            StarkProof::<U> {
                tuple_merkle_root,
                linear_combination_merkle_root,
                air_tuple_authentication_paths,
                next_air_tuple_authentication_paths,
                bc_tuple_authentication_paths,
                lc_tuple_authentication_paths,
                linear_combination_fri,
                index_picker_preimage,
            },
            index,
        ))
    }
}

impl StarkProof<BigInt> {
    pub fn verify(
        &self,
        claim: MimcClaim<PrimeFieldElementBig>,
        round_constants: Vec<PrimeFieldElementBig>,
        omega: PrimeFieldElementBig,
        num_steps: i128,
        expansion_factor: i128,
    ) -> Result<(), Box<dyn Error>> {
        let field = claim.input.field;
        let omicron = omega.mod_pow(Into::<BigInt>::into(expansion_factor));
        let omega_domain = omega.get_generator_domain();
        let omicron_domain = omicron.get_generator_domain();
        let extended_domain_length = (num_steps + 1) * expansion_factor;
        let xlast = omicron_domain.last().unwrap();

        // Verify low-degreeness of linear combination
        low_degree_test::verify_bigint(self.linear_combination_fri.clone(), field.q.clone())?;

        // Verify that linear combination matches that of the committed tuple tree
        // get all indices (a,b) of first FRI round
        let abc_indices: Vec<(usize, usize, usize)> =
            self.linear_combination_fri.get_abc_indices(0);
        let mut ab_indices: Vec<usize> = vec![];
        for (a, b, _) in abc_indices.iter() {
            ab_indices.push(*a);
            ab_indices.push(*b);
        }
        // Verify that Linear combination authentication paths match those committed to in the root hash
        // Note that the authentication paths *should* be checked in the verifier of the low-degree test.
        // So we don't need to check that here.
        let lc_tuple_authentication_paths: Vec<
            CompressedAuthenticationPath<(BigInt, BigInt, BigInt)>,
        > = self.lc_tuple_authentication_paths.clone();
        let lc_paths_valid = MerkleTree::verify_multi_proof(
            self.tuple_merkle_root,
            &ab_indices,
            &lc_tuple_authentication_paths,
        );
        if !lc_paths_valid {
            return Err(Box::new(
                StarkVerifyError::LinearCombinationAuthenticationPath,
            ));
        }

        // Verify linear relation on revealed elements in the tuple Merkle tree
        let lc_coefficients = get_linear_combination_coefficients(field, &self.tuple_merkle_root);
        for j in 0..self.linear_combination_fri.s as usize * 2 {
            let x = omega_domain[ab_indices[j]].clone();
            let x_power_ns_plus_1 = omega_domain
                [ab_indices[j] * (num_steps + 1) as usize % extended_domain_length as usize]
                .clone();
            let x_power_ns_plus_3 = omega_domain
                [ab_indices[j] * (num_steps + 3) as usize % extended_domain_length as usize]
                .clone();
            let extended_computational_trace: PrimeFieldElementBig = PrimeFieldElementBig::new(
                self.lc_tuple_authentication_paths[j].get_value().0.clone(),
                omega.field,
            );
            let shifted_trace_codeword =
                extended_computational_trace.clone() * x_power_ns_plus_1.clone();
            let transition_quotient_codeword: PrimeFieldElementBig = PrimeFieldElementBig::new(
                self.lc_tuple_authentication_paths[j].get_value().1.clone(),
                omega.field,
            );
            let shifted_transition_quotient_codeword =
                transition_quotient_codeword.clone() * x.clone();
            let boundary_quotient_codeword = PrimeFieldElementBig::new(
                self.lc_tuple_authentication_paths[j].get_value().2.clone(),
                omega.field,
            );
            let shifted_boundary_quotient_codeword =
                boundary_quotient_codeword.clone() * x_power_ns_plus_3.clone();
            let right_hand_side: PrimeFieldElementBig = get_linear_combination(
                &lc_coefficients,
                PolynomialEvaluations {
                    extended_computational_trace: extended_computational_trace.clone(),
                    shifted_trace_codeword,
                    transition_quotient_codeword: transition_quotient_codeword.clone(),
                    shifted_transition_quotient_codeword,
                    boundary_quotient_codeword,
                    shifted_boundary_quotient_codeword,
                },
            );
            let left_hand_side: PrimeFieldElementBig = PrimeFieldElementBig::new(
                self.linear_combination_fri.ab_proofs[0][j].get_value(),
                omega.field,
            );
            if left_hand_side != right_hand_side {
                return Err(Box::new(StarkVerifyError::LinearCombinationTupleMismatch(
                    j,
                )));
            }
        }

        // Calculate the transition zerofier and round constant interpolation
        let (tz_num, tz_den): (
            Polynomial<PrimeFieldElementBig>,
            Polynomial<PrimeFieldElementBig>,
        ) = get_transition_zerofier_polynomials(num_steps as usize, xlast);
        let tz_pol = tz_num / tz_den;
        let rcc = get_round_constants_coefficients(&omicron, &round_constants);
        let rc_pol = Polynomial { coefficients: rcc };

        let num_air_checks = self.air_tuple_authentication_paths.len();
        let num_bc_checks = self.bc_tuple_authentication_paths.len();
        let index_picker_hashes = utils::get_n_hash_rounds(
            &self.index_picker_preimage,
            (num_air_checks + num_bc_checks) as u32,
        );
        let air_indices: Vec<usize> = index_picker_hashes[0..num_air_checks]
            .iter()
            .map(|d| utils::get_index_from_bytes(d, extended_domain_length as usize))
            .collect();
        let next_air_indices: Vec<usize> = air_indices
            .iter()
            .map(|x| (x + expansion_factor as usize) % extended_domain_length as usize)
            .collect::<Vec<usize>>();
        let valid_air_paths = MerkleTree::verify_multi_proof(
            self.tuple_merkle_root,
            &air_indices,
            &self.air_tuple_authentication_paths,
        );
        if !valid_air_paths {
            return Err(Box::new(StarkVerifyError::BadAirPaths));
        }

        let valid_next_air_paths = MerkleTree::verify_multi_proof(
            self.tuple_merkle_root,
            &next_air_indices,
            &self.next_air_tuple_authentication_paths,
        );
        if !valid_next_air_paths {
            return Err(Box::new(StarkVerifyError::BadNextAirPaths));
        }
        #[allow(clippy::needless_range_loop)]
        for j in 0..num_air_checks as usize {
            // Verify transition constraint relation
            let index = air_indices[j];
            let x = omega_domain[index].clone();
            let transition_quotient_value: PrimeFieldElementBig = PrimeFieldElementBig::new(
                self.air_tuple_authentication_paths[j].clone().get_value().1,
                omega.field,
            );
            let next_extended_computational_trace_value = PrimeFieldElementBig::new(
                self.next_air_tuple_authentication_paths[j]
                    .clone()
                    .get_value()
                    .0,
                omega.field,
            );
            let extended_computational_trace_value = PrimeFieldElementBig::new(
                self.air_tuple_authentication_paths[j].clone().get_value().0,
                omega.field,
            );

            // Verify AIR transition identity
            if transition_quotient_value * tz_pol.evaluate(&x)
                != rc_pol.evaluate(&x)
                    + extended_computational_trace_value
                        .clone()
                        .mod_pow(Into::<BigInt>::into(3))
                    - next_extended_computational_trace_value
            {
                return Err(Box::new(StarkVerifyError::BadAirTransitionIdentity(j)));
            }
        }

        // verify boundary constraints
        let bz_pol = get_boundary_zerofier_polynomial(xlast);
        let bc_pol = get_boundary_constraint_polynomial(&claim.input, &claim.output, xlast);
        let bc_indices: Vec<usize> = index_picker_hashes
            [num_air_checks..(num_air_checks + num_bc_checks)]
            .iter()
            .map(|d| utils::get_index_from_bytes(d, extended_domain_length as usize))
            .collect();

        let valid_bc_paths = MerkleTree::verify_multi_proof(
            self.tuple_merkle_root,
            &bc_indices,
            &self.bc_tuple_authentication_paths,
        );
        if !valid_bc_paths {
            return Err(Box::new(StarkVerifyError::BadBoundaryConditionPaths));
        }
        #[allow(clippy::needless_range_loop)]
        for j in 0..num_bc_checks {
            let index = bc_indices[j];
            let x = omega_domain[index].clone();
            let extended_computational_trace_value = PrimeFieldElementBig::new(
                self.bc_tuple_authentication_paths[j].clone().get_value().0,
                omega.field,
            );
            let boundary_quotient_value: PrimeFieldElementBig = PrimeFieldElementBig::new(
                self.bc_tuple_authentication_paths[j].clone().get_value().2,
                omega.field,
            );
            if extended_computational_trace_value - bc_pol.evaluate(&x)
                != boundary_quotient_value * bz_pol.evaluate(&x)
            {
                return Err(Box::new(StarkVerifyError::BadAirBoundaryIndentity(j)));
            }
        }

        Ok(())
    }
}

struct SanityCheckArgs<'a> {
    num_steps: usize,
    extended_computational_trace_bigint: Vec<BigInt>,
    field: PrimeFieldBig,
    security_checks: usize,
    omega: PrimeFieldElementBig<'a>,
    boundary_quotient_codeword_bigint: &'a [BigInt],
    transition_quotient_codeword_bigint: &'a [BigInt],
    shifted_transition_quotient_codeword: &'a [PrimeFieldElementBig<'a>],
    shifted_boundary_quotient_codeword: &'a [PrimeFieldElementBig<'a>],
    shifted_trace_codeword: &'a [PrimeFieldElementBig<'a>],
}

fn stark_of_mimc_sanity_checks(args: SanityCheckArgs) -> bool {
    let num_steps = args.num_steps;
    let extended_computational_trace_bigint = args.extended_computational_trace_bigint;
    let field = args.field;
    let security_checks = args.security_checks;
    let omega = args.omega;
    let boundary_quotient_codeword_bigint = args.boundary_quotient_codeword_bigint;
    let transition_quotient_codeword_bigint = args.transition_quotient_codeword_bigint;
    let shifted_transition_quotient_codeword = args.shifted_transition_quotient_codeword;
    let shifted_boundary_quotient_codeword = args.shifted_boundary_quotient_codeword;
    let shifted_trace_codeword = args.shifted_trace_codeword;

    // SANITY CHECKS START
    let mut output: Vec<u8> = vec![];
    // sanity check: low degree of trace
    let max_degree_ect = num_steps as u32;
    let low_degree_proof_ect = low_degree_test::prover_bigint(
        &extended_computational_trace_bigint,
        field.q.clone(),
        max_degree_ect,
        security_checks,
        &mut output,
        omega.value.clone(),
    )
    .unwrap();
    let verify: Result<(), low_degree_test::ValidationError> =
        low_degree_test::verify_bigint(low_degree_proof_ect, field.q.clone());
    match verify {
        Ok(_) => println!(
            "Succesfully verified low degree ({}) of extended computational trace",
            max_degree_ect
        ),
        Err(_err) => return false,
    }

    // sanity check: low degree of boundary quotient
    let max_degree_bq = num_steps as u32;
    let low_degree_proof_bq = low_degree_test::prover_bigint(
        &boundary_quotient_codeword_bigint,
        field.q.clone(),
        max_degree_bq,
        security_checks,
        &mut output,
        omega.value.clone(),
    )
    .unwrap();
    let verify: Result<(), low_degree_test::ValidationError> =
        low_degree_test::verify_bigint(low_degree_proof_bq, field.q.clone());
    match verify {
        Ok(_) => println!(
            "Succesfully verified low degree ({}) of boundary quotient",
            max_degree_bq
        ),
        Err(_err) => return false,
    }

    // sanity check: low degree of transition quotient
    let max_degree_tq = ((num_steps + 1) * 2 - 1) as u32;
    let low_degree_proof_tq = low_degree_test::prover_bigint(
        &transition_quotient_codeword_bigint,
        field.q.clone(),
        max_degree_tq,
        security_checks,
        &mut output,
        omega.value.clone(),
    )
    .unwrap();
    let verify: Result<(), low_degree_test::ValidationError> =
        low_degree_test::verify_bigint(low_degree_proof_tq, field.q.clone());
    match verify {
        Ok(_) => println!(
            "Succesfully verified low degree ({}) of transition quotient",
            max_degree_tq
        ),
        Err(_err) => return false,
    }

    // sanity check: low degee of shifted transition quotient
    let max_degree_shifted_tq = ((num_steps + 1) * 2 - 1) as u32;
    let shifted_transition_quotient_codeword_bi = shifted_transition_quotient_codeword
        .iter()
        .map(|x| x.value.clone())
        .collect::<Vec<BigInt>>();
    let low_degree_proof_shifted_tq = low_degree_test::prover_bigint(
        &shifted_transition_quotient_codeword_bi,
        field.q.clone(),
        max_degree_shifted_tq,
        security_checks,
        &mut output,
        omega.value.clone(),
    )
    .unwrap();
    let verify: Result<(), low_degree_test::ValidationError> =
        low_degree_test::verify_bigint(low_degree_proof_shifted_tq, field.q.clone());
    match verify {
        Ok(_) => println!(
            "Succesfully verified low degree ({}) of shifted transition quotient",
            max_degree_tq
        ),
        Err(_err) => return false,
    }

    // sanity check: low degree of shifted boundary quotient
    let max_degree_shifted_bq = ((num_steps + 1) * 2 - 1) as u32;
    let shifted_boundary_quotient_codeword_bi = shifted_boundary_quotient_codeword
        .iter()
        .map(|x| x.value.clone())
        .collect::<Vec<BigInt>>();
    let low_degree_proof_shifted_bq = low_degree_test::prover_bigint(
        &shifted_boundary_quotient_codeword_bi,
        field.q.clone(),
        max_degree_shifted_bq,
        security_checks,
        &mut output,
        omega.value.clone(),
    )
    .unwrap();
    let verify: Result<(), low_degree_test::ValidationError> =
        low_degree_test::verify_bigint(low_degree_proof_shifted_bq, field.q.clone());
    match verify {
        Ok(_) => println!(
            "Succesfully verified low degree ({}) of shifted boundary quotient",
            max_degree_tq
        ),
        Err(_err) => return false,
    }

    // sanity check: low degree of shifted trace
    let max_degree_shifted_ti = ((num_steps + 1) * 2 - 1) as u32;
    let shifted_trace_codeword_bi = shifted_trace_codeword
        .iter()
        .map(|x| x.value.clone())
        .collect::<Vec<BigInt>>();
    let low_degree_proof_shifted_ti = low_degree_test::prover_bigint(
        &shifted_trace_codeword_bi,
        field.q.clone(),
        max_degree_shifted_ti,
        security_checks,
        &mut output,
        omega.value,
    )
    .unwrap();
    let verify: Result<(), low_degree_test::ValidationError> =
        low_degree_test::verify_bigint(low_degree_proof_shifted_ti, field.q);
    match verify {
        Ok(_) => println!(
            "Succesfully verified low degree ({}) of shifted trace interpolant",
            max_degree_tq
        ),
        Err(_err) => return false,
    }

    // SANITY CHECKS END
    true
}

pub fn stark_of_mimc_prove(
    security_checks: usize,
    num_steps: usize,
    expansion_factor: usize,
    omega: PrimeFieldElementBig,
    mimc_claim: &MimcClaim<PrimeFieldElementBig>,
    transcript: &mut Vec<u8>,
) -> Result<StarkProof<BigInt>, StarkProofError> {
    // Omega is the generator of the big domain
    // Omicron is the generator of the small domain
    let omicron: PrimeFieldElementBig = omega.mod_pow(Into::<BigInt>::into(expansion_factor));
    let extended_domain_length: usize = (num_steps + 1) * expansion_factor;
    let field: &PrimeFieldBig = omega.field;

    // compute computational trace
    let computational_trace: Vec<PrimeFieldElementBig> =
        mimc_forward(&mimc_claim.input, num_steps, &mimc_claim.round_constants);

    // Verify that the MiMC claim is correct
    if mimc_claim.output != *computational_trace.last().unwrap() {
        return Err(StarkProofError::InputOutputMismatch);
    }

    // compute low-degree extension of computational trace
    let (extended_computational_trace, trace_interpolant): (
        Vec<PrimeFieldElementBig>,
        Polynomial<PrimeFieldElementBig>,
    ) = get_extended_computational_trace(
        &omega,
        &omicron,
        num_steps,
        expansion_factor,
        &computational_trace,
    );

    // compute low-degree extension of the round constants polynomial
    let extended_round_constants = get_extended_round_constant(
        &omega,
        &omicron,
        num_steps,
        expansion_factor,
        &mimc_claim.round_constants,
    );

    // evaluate and interpolate AIR
    let mut air_codeword = Vec::<PrimeFieldElementBig>::with_capacity(extended_domain_length);
    for i in 0..extended_domain_length {
        air_codeword.push(
            extended_computational_trace[i].mod_pow(Into::<BigInt>::into(3))
                + extended_round_constants[i].clone()
                - extended_computational_trace[(i + expansion_factor) % extended_domain_length]
                    .clone(),
        );
    }

    // It's important to interpolate across the *extended* domain, not the original smaller domain, because the degree of air(x) is greater than num_steps
    let air_polynomial_coefficients = intt(&air_codeword, &omega);
    let air_polynomial = Polynomial {
        coefficients: air_polynomial_coefficients,
    };

    let omega_domain: Vec<PrimeFieldElementBig> = omega.get_generator_domain();
    let omicron_domain: Vec<PrimeFieldElementBig> = omicron.get_generator_domain();
    let xlast: &PrimeFieldElementBig = omicron_domain.last().unwrap();

    // compute transition-zerofier polynomial
    let (transition_zerofier_numerator_polynomial, transition_zerofier_denominator_polynomial) =
        get_transition_zerofier_polynomials(num_steps, xlast);

    // compute the transition-quotient polynomial
    let (transition_quotient_polynomial, rem) = (air_polynomial.clone()
        * transition_zerofier_denominator_polynomial.clone())
    .divide(transition_zerofier_numerator_polynomial.clone());
    // Perform sanity check that remainder of division by transition-zerofier is zero
    if !(rem.is_zero()) {
        return Err(StarkProofError::NonZeroTransitionRemainder);
    }

    // Compute the codeword of the transition-quotient polynomial in the entire omega domain,
    let mut transition_quotient_coefficients = transition_quotient_polynomial.coefficients.clone();
    transition_quotient_coefficients.append(&mut vec![
        omega.ring_zero();
        extended_domain_length
            - transition_quotient_coefficients.len()
    ]);
    let transition_quotient_codeword = ntt(&transition_quotient_coefficients, &omega);

    // compute the boundary-zerofier
    let boundary_zerofier_polynomial = get_boundary_zerofier_polynomial(xlast);

    let boundary_constraint_polynomial =
        get_boundary_constraint_polynomial(&mimc_claim.input, &mimc_claim.output, xlast);

    // compute the boundary-quotient polynomial and codeword
    let (boundary_quotient_polynomial, bq_rem) =
        (trace_interpolant - boundary_constraint_polynomial).divide(boundary_zerofier_polynomial);
    if !(bq_rem.is_zero()) {
        return Err(StarkProofError::NonZeroBoundaryRemainder);
    }

    let mut boundary_constraint_coefficients_padded =
        boundary_quotient_polynomial.coefficients.clone();
    boundary_constraint_coefficients_padded.append(&mut vec![
        omega.ring_zero();
        expansion_factor * (num_steps + 1)
            - boundary_quotient_polynomial
                .coefficients
                .len()
    ]);
    let boundary_quotient_codeword = ntt(&boundary_constraint_coefficients_padded, &omega);

    // Commit to all evaluations by constructing a Merkle tree of the polynomial evaluations
    // TODO: We also need the offset values of the ect, since this is needed to verify that
    // `air(x) = TQ(x) * Z_t(x)`.
    let polynomial_evaluations: Vec<(BigInt, BigInt, BigInt)> = extended_computational_trace
        .iter()
        .zip(transition_quotient_codeword.iter())
        .zip(boundary_quotient_codeword.iter())
        .map(|((ect, tq), bq)| {
            (
                ect.to_owned().value,
                tq.to_owned().value,
                bq.to_owned().value,
            )
        })
        .collect::<Vec<(BigInt, BigInt, BigInt)>>();
    let tuple_merkle_tree: MerkleTree<(BigInt, BigInt, BigInt)> =
        MerkleTree::from_vec(&polynomial_evaluations);

    let lc_coefficients =
        get_linear_combination_coefficients(&field, &tuple_merkle_tree.get_root());

    // compute shifted trace codeword
    let mut shifted_trace_codeword: Vec<PrimeFieldElementBig> =
        extended_computational_trace.clone();
    let mut xi: PrimeFieldElementBig = omega.ring_one();
    for stc in shifted_trace_codeword.iter_mut() {
        *stc = stc.to_owned() * xi.clone();
        xi = xi * omega_domain[num_steps + 1].clone();
    }

    // compute shifted transition quotient codeword
    let mut shifted_transition_quotient_codeword: Vec<PrimeFieldElementBig> =
        transition_quotient_codeword.clone();
    for i in 0..extended_domain_length {
        shifted_transition_quotient_codeword[i] =
            shifted_transition_quotient_codeword[i].clone() * omega_domain[i].clone();
    }

    // compute shifted boundary quotient codeword
    let mut shifted_boundary_quotient_codeword: Vec<PrimeFieldElementBig> =
        boundary_quotient_codeword.clone();
    xi = omega.ring_one();
    for sbqc in shifted_boundary_quotient_codeword.iter_mut() {
        *sbqc = sbqc.to_owned() * xi.clone();
        xi = xi * omega_domain[num_steps + 3].clone();
    }

    // Compute linear combination of previous polynomial values
    let polynomial_evaluations = (0..extended_domain_length)
        .map(|i| PolynomialEvaluations {
            extended_computational_trace: extended_computational_trace[i].clone(),
            shifted_trace_codeword: shifted_trace_codeword[i].clone(),
            transition_quotient_codeword: transition_quotient_codeword[i].clone(),
            shifted_transition_quotient_codeword: shifted_transition_quotient_codeword[i].clone(),
            boundary_quotient_codeword: boundary_quotient_codeword[i].clone(),
            shifted_boundary_quotient_codeword: shifted_boundary_quotient_codeword[i].clone(),
        })
        .collect::<Vec<PolynomialEvaluations<PrimeFieldElementBig>>>();
    let linear_combination_codeword =
        get_linear_combinations(&lc_coefficients, polynomial_evaluations)
            .iter()
            .map(|x| x.value.clone())
            .collect::<Vec<BigInt>>();

    let linear_combination_mt = MerkleTree::from_vec(&linear_combination_codeword);

    // Compute the FRI low-degree proofs
    let extended_computational_trace_bigint = extended_computational_trace
        .iter()
        .map(|x| x.value.clone())
        .collect::<Vec<BigInt>>();
    let boundary_quotient_codeword_bigint = boundary_quotient_codeword
        .iter()
        .map(|x| x.value.clone())
        .collect::<Vec<BigInt>>();
    let transition_quotient_codeword_bigint = transition_quotient_codeword
        .iter()
        .map(|x| x.value.clone())
        .collect::<Vec<BigInt>>();
    let linear_combination_evaluations_bigint = linear_combination_codeword;

    let sane = stark_of_mimc_sanity_checks(SanityCheckArgs {
        num_steps,
        extended_computational_trace_bigint,
        field: field.clone(),
        security_checks: 128,
        omega: omega.clone(),
        boundary_quotient_codeword_bigint: &boundary_quotient_codeword_bigint,
        transition_quotient_codeword_bigint: &transition_quotient_codeword_bigint,
        shifted_transition_quotient_codeword: &shifted_transition_quotient_codeword,
        shifted_boundary_quotient_codeword: &shifted_boundary_quotient_codeword,
        shifted_trace_codeword: &shifted_trace_codeword,
    });
    assert!(sane);

    // let max_degree_lc = num_steps as u32;
    let max_degree_lc = ((num_steps + 1) * 2 - 1) as u32;
    println!("max_degree of linear combination is: {}", max_degree_lc);
    transcript.append(&mut tuple_merkle_tree.get_root().to_vec());
    let low_degree_proof_lc_result = low_degree_test::prover_bigint(
        &linear_combination_evaluations_bigint,
        field.q.clone(),
        max_degree_lc,
        security_checks,
        transcript,
        omega.value.clone(),
    );

    // sanity check: low degree of linear combination
    let linear_combination_fri: LowDegreeProof<BigInt>;
    match low_degree_proof_lc_result {
        Err(_err) => return Err(StarkProofError::HighDegreeLinearCombination),
        Ok(proof) => {
            println!(
                "Successfully verified low degree ({}) of linear combination!",
                max_degree_lc
            );
            linear_combination_fri = proof;
        }
    }
    let verify: Result<(), low_degree_test::ValidationError> =
        low_degree_test::verify_bigint(linear_combination_fri.clone(), field.q.clone());
    match verify {
        Ok(_) => (),
        Err(_err) => {
            println!(
                "\n\n\n\nFailed to low degreeness of linear combination values.\n\n Coefficients: {:?}\n\nCodeword: {:?}\n\nDomain: {:?}",
                lc_coefficients, linear_combination_evaluations_bigint, omega_domain
            );
            return Err(StarkProofError::HighDegreeLinearCombination);
        }
    }

    // enable verification of linear combination

    // Produce authentication paths for the relevant codewords
    let abc_indices: Vec<(usize, usize, usize)> = linear_combination_fri.get_abc_indices(0);
    // let indices = ab_indices.iter().map(|(a, b)| )
    // todo: use https://users.rust-lang.org/t/flattening-a-vector-of-tuples/11409/2
    let mut ab_indices: Vec<usize> = vec![];
    for (a, b, _) in abc_indices.iter() {
        ab_indices.push(*a);
        ab_indices.push(*b);
    }

    let lc_tuple_authentication_paths: Vec<CompressedAuthenticationPath<(BigInt, BigInt, BigInt)>> =
        tuple_merkle_tree.get_multi_proof(&ab_indices);

    // enable verification of transition constraint

    // Need:
    // - New source of randomness, use FRI's `output` Vec<u8>
    // - Use these to pick new authentication paths, both for tuple_authentication_paths, next_tuple_authentication_paths
    let security_level = 128;
    let num_air_checks = security_level;
    let index_picker_hashes: Vec<[u8; 32]> =
        utils::get_n_hash_rounds(&transcript, 2 * security_level as u32);
    // Before transcript is manipulated, store the preimage that was used to pick the
    // indices, as this is a field of the STARK proof
    let index_picker_preimage = transcript.clone();

    let air_indices: Vec<usize> = index_picker_hashes[0..num_air_checks]
        .iter()
        .map(|d| utils::get_index_from_bytes(d, extended_domain_length))
        .collect();
    let next_air_indices: Vec<usize> = air_indices
        .iter()
        .map(|x| (x + expansion_factor) % extended_domain_length)
        .collect::<Vec<usize>>();
    let air_authentication_paths = tuple_merkle_tree.get_multi_proof(air_indices.as_slice());
    let next_air_authentication_paths =
        tuple_merkle_tree.get_multi_proof(next_air_indices.as_slice());

    // enable boundary constraint check
    let num_boundary_checks = security_level;
    let bc_indices: Vec<usize> = index_picker_hashes
        [num_air_checks..(num_air_checks + num_boundary_checks)]
        .iter()
        .map(|d| utils::get_index_from_bytes(d, extended_domain_length))
        .collect();

    let bc_authentication_paths = tuple_merkle_tree.get_multi_proof(&bc_indices);

    // Manipulate the transcript to include whole proof
    // Add LC merkle root
    transcript.append(&mut bincode::serialize(&linear_combination_mt.get_root()).unwrap());

    // Add LC tuple authentication paths
    let mut serialized_lc_tuple_authentication_paths =
        bincode::serialize(&lc_tuple_authentication_paths).unwrap();
    transcript.append(
        &mut bincode::serialize(&(serialized_lc_tuple_authentication_paths.len() as u32)).unwrap(),
    );
    transcript.append(&mut serialized_lc_tuple_authentication_paths);

    // Add Next AIR Tuple authentication paths
    let mut serialized_next_air_authentication_paths =
        bincode::serialize(&next_air_authentication_paths).unwrap();
    transcript.append(
        &mut bincode::serialize(&(serialized_next_air_authentication_paths.len() as u32)).unwrap(),
    );
    transcript.append(&mut serialized_next_air_authentication_paths);

    // Add AIR Tuple authentication paths
    let mut serialized_air_authentication_paths =
        bincode::serialize(&air_authentication_paths).unwrap();
    transcript.append(
        &mut bincode::serialize(&(serialized_air_authentication_paths.len() as u32)).unwrap(),
    );
    transcript.append(&mut serialized_air_authentication_paths);

    // Add AIR boundary conditions authentication paths
    let mut serialized_bc_authentication_paths =
        bincode::serialize(&bc_authentication_paths).unwrap();
    transcript.append(
        &mut bincode::serialize(&(serialized_bc_authentication_paths.len() as u32)).unwrap(),
    );
    transcript.append(&mut serialized_bc_authentication_paths);

    Ok(StarkProof {
        tuple_merkle_root: tuple_merkle_tree.get_root(),
        linear_combination_merkle_root: linear_combination_mt.get_root(),
        lc_tuple_authentication_paths,
        next_air_tuple_authentication_paths: next_air_authentication_paths,
        air_tuple_authentication_paths: air_authentication_paths,
        bc_tuple_authentication_paths: bc_authentication_paths,
        linear_combination_fri,
        index_picker_preimage,
    })
}

#[cfg(test)]
mod test_modular_arithmetic {
    use super::*;
    use crate::shared_math::prime_field_element::PrimeField;
    use crate::shared_math::prime_field_element_big::PrimeFieldBig;

    fn b(x: i128) -> BigInt {
        Into::<BigInt>::into(x)
    }

    #[test]
    fn mimc_big_test() {
        let no_steps = 3;
        let expansion_factor = 4;
        let security_factor = 10;
        let field = PrimeFieldBig::new(b(5 * 2i128.pow(25) + 1));
        let round_constants_raw: Vec<i128> = vec![7, 256, 117];
        let round_constants: Vec<PrimeFieldElementBig> = round_constants_raw
            .iter()
            .map(|x| PrimeFieldElementBig::new(b(x.to_owned()), &field)) // TODO: FIX!! REPLACE value BY x
            .collect::<Vec<PrimeFieldElementBig>>();
        let (g2_option, _) = field.get_primitive_root_of_unity((no_steps + 1) * expansion_factor);
        let omega = g2_option.unwrap();
        let omicron = omega.mod_pow(b(expansion_factor));
        println!("Found omega = {}", omega);
        println!("Found omicron = {}", omicron);

        for i in 0..5 {
            println!("i = {}", i);
            let mimc_input = PrimeFieldElementBig::new(b(i), &field);
            let mimc_trace = mimc_forward(&mimc_input, no_steps as usize, &round_constants);
            let mimc_output = mimc_trace[no_steps as usize].clone();
            println!("\n\n\n\n\n\n\n\n\n\nmimc_input = {}", mimc_input);
            println!("mimc_output = {}", mimc_output);
            println!("x_last = {}", omicron.mod_pow(b(no_steps - 1)));
            let mut mimc_claim = MimcClaim::<PrimeFieldElementBig> {
                input: mimc_input.clone(),
                output: mimc_output.clone(),
                round_constants: round_constants.clone(),
            };
            let mut transcript: Vec<u8> = vec![];
            let mut stark_res = stark_of_mimc_prove(
                security_factor,
                no_steps as usize,
                expansion_factor as usize,
                omega.clone(),
                &mimc_claim,
                &mut transcript,
            );

            let mut stark_proof: StarkProof<BigInt> = match stark_res {
                Ok(stark_proof) => stark_proof,
                Err(_err) => panic!("Failed to produce STARK proof"),
            };

            // Verify that proof can be deserialized correctly
            let (deserialized_proof, _) =
                StarkProof::<BigInt>::from_serialization(transcript.clone(), 0).unwrap();
            assert_eq!(stark_proof, deserialized_proof);
            assert!(stark_proof
                .verify(
                    mimc_claim.clone(),
                    round_constants.clone(),
                    omega.clone(),
                    no_steps,
                    expansion_factor,
                )
                .is_ok());

            // Verify that the transcript can be preloaded when the STARK prover begins
            transcript = vec![123, 45, 67, 89, 52];
            stark_res = stark_of_mimc_prove(
                security_factor,
                no_steps as usize,
                expansion_factor as usize,
                omega.clone(),
                &mimc_claim,
                &mut transcript,
            );

            stark_proof = match stark_res {
                Ok(stark_proof) => stark_proof,
                Err(_err) => panic!("Failed to produce STARK proof"),
            };

            // Verify that proof can be deserialized correctly
            let (deserialized_proof, _) =
                StarkProof::<BigInt>::from_serialization(transcript.clone(), 5).unwrap();
            assert_eq!(stark_proof, deserialized_proof);

            // Verify that false Merkle roots result in the correct verification errors
            stark_proof.tuple_merkle_root[31] ^= 1;
            let mut bad_verify_result = stark_proof.verify(
                mimc_claim.clone(),
                round_constants.clone(),
                omega.clone(),
                no_steps,
                expansion_factor,
            );
            assert!(bad_verify_result.is_err());
            println!("Error is: {:?}", bad_verify_result.as_ref().err());
            assert!(bad_verify_result.err().unwrap().is::<StarkVerifyError>());

            // Reset bad Merkle root value, and verify that a bad Merkle root in the FRI
            // proof gives an error
            stark_proof.tuple_merkle_root[31] ^= 1;
            stark_proof.linear_combination_fri.merkle_roots[0][31] ^= 1;
            bad_verify_result = stark_proof.verify(
                mimc_claim.clone(),
                round_constants.clone(),
                omega.clone(),
                no_steps,
                expansion_factor,
            );
            assert!(bad_verify_result.is_err());
            println!("Error is now: {:?}", bad_verify_result.as_ref().err());
            assert!(bad_verify_result
                .err()
                .unwrap()
                .is::<low_degree_test::ValidationError>());

            // Prove with alse MiMC claim and verify that it fails
            mimc_claim.output = mimc_input.clone();
            stark_res = stark_of_mimc_prove(
                security_factor,
                no_steps as usize,
                expansion_factor as usize,
                omega.clone(),
                &mimc_claim,
                &mut transcript,
            );
            assert!(stark_res.is_err());
            assert_eq!(Some(StarkProofError::InputOutputMismatch), stark_res.err());
        }
    }

    #[test]
    fn mimc_forward_small() {
        let field = PrimeField::new(17);
        let input = PrimeFieldElement::new(6, &field);
        let round_constant = vec![
            PrimeFieldElement::new(6, &field),
            PrimeFieldElement::new(2, &field),
            PrimeFieldElement::new(1, &field),
            PrimeFieldElement::new(9, &field),
        ];
        let result: Vec<PrimeFieldElement> = mimc_forward_i128(&input, 7, &round_constant);

        // Result was verified on WolframAlpha: works for input = 6 mod 17
        assert_eq!(13, result.last().unwrap().value);

        for j in 0..10 {
            for i in 0..16 {
                let input2 = PrimeFieldElement::new(i, &field);
                let result2 = mimc_forward_i128(&input2, j, &round_constant);
                assert_eq!(
                    input2,
                    mimc_backward(&result2.last().unwrap(), j, &round_constant)
                );
            }
        }
    }

    // #[test]
    // fn small_stark_of_mimc() {
    //     #![allow(clippy::just_underscores_and_digits)]
    //     // Create a field with a 8192th primitive root of unity and a (8*8192)th primitive root of unity
    //     // This field is mod 65537 and the roots are 6561, 3, respectively.

    //     // Use these to index into m and l.
    //     // Then generate a proof that lc_codeword is of low degree (steps * 2)
    //     let field = PrimeField::new(65537);
    //     stark_of_mimc_i128(
    //         80,
    //         8192,
    //         8,
    //         65537,
    //         PrimeFieldElement::new(3, &field),
    //         PrimeFieldElement::new(827, &field),
    //     );
    // }
}
