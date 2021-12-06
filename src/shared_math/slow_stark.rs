use num_bigint::BigInt;
use rand::{RngCore, SeedableRng};

use rand_pcg::Pcg64;

use crate::shared_math::traits::IdentityValues;
use crate::util_types::merkle_tree::{MerkleTree, PartialAuthenticationPath};
use std::fmt;
use std::{collections::HashMap, error::Error};

use crate::{shared_math::polynomial::Polynomial, util_types::proof_stream::ProofStream, utils};

use super::fri::Fri;
use super::other::log_2_ceil;
use super::stark::BoundaryConstraint;
use super::{
    mpolynomial::MPolynomial,
    prime_field_element_big::{PrimeFieldBig, PrimeFieldElementBig},
};

// A hashmap from register value to (x, y) value of boundary constraint
pub type BoundaryConstraintsMap<'a> =
    HashMap<usize, (PrimeFieldElementBig<'a>, PrimeFieldElementBig<'a>)>;

pub struct Stark<'a> {
    expansion_factor: usize,
    field: PrimeFieldBig,
    fri: Fri,
    field_generator: PrimeFieldElementBig<'a>,
    randomizer_count: usize,
    omega: PrimeFieldElementBig<'a>,
    pub omicron: PrimeFieldElementBig<'a>, // omicron = omega^expansion_factor
    omicron_domain: Vec<PrimeFieldElementBig<'a>>,
    original_trace_length: usize,
    randomized_trace_length: usize,
    register_count: usize,
}

impl<'a> Stark<'a> {
    pub fn new(
        field: &'a PrimeFieldBig,
        expansion_factor: usize,
        colinearity_check_count: usize,
        register_count: usize,
        cycle_count: usize,
        transition_constraints_degree: usize,
        generator: PrimeFieldElementBig<'a>,
    ) -> Self {
        let num_randomizers = 4 * colinearity_check_count;
        let original_trace_length = cycle_count;
        let randomized_trace_length = original_trace_length + num_randomizers;
        let omicron_domain_length =
            1usize << log_2_ceil((randomized_trace_length * transition_constraints_degree) as u64);
        let fri_domain_length = omicron_domain_length * expansion_factor;
        let omega = field
            .get_primitive_root_of_unity(fri_domain_length as i128)
            .0
            .unwrap();
        let omicron = omega.mod_pow(expansion_factor.into());

        // Verify omega and omicron values
        assert!(
            omicron.mod_pow(omicron_domain_length.into()).is_one(),
            "omicron must have correct order"
        );
        assert!(
            !omicron.mod_pow((omicron_domain_length / 2).into()).is_one(),
            "omicron must have correct primitive order"
        );
        assert!(
            omega.mod_pow(fri_domain_length.into()).is_one(),
            "omicron must have correct order"
        );
        assert!(
            !omega.mod_pow((fri_domain_length / 2).into()).is_one(),
            "omicron must have correct primitive order"
        );

        let omicron_domain = field
            .get_power_series(omicron.value.clone())
            .into_iter()
            .map(|x| PrimeFieldElementBig::new(x, field))
            .collect();

        let fri = Fri::new(
            generator.value.clone(),
            omega.value.clone(),
            fri_domain_length,
            expansion_factor,
            colinearity_check_count,
            omega.field.q.clone(),
        );

        Self {
            expansion_factor,
            field: field.to_owned(),
            field_generator: generator,
            randomizer_count: num_randomizers,
            omega,
            omicron,
            omicron_domain,
            original_trace_length,
            randomized_trace_length,
            register_count,
            fri,
        }
    }
}

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
pub enum MerkleProofError {
    BoundaryQuotientError(usize),
    RandomizerError,
}

#[derive(Debug, PartialEq, Eq)]
pub enum StarkVerifyError {
    BadAirPaths,
    BadNextAirPaths,
    BadAirBoundaryIndentity(usize),
    BadAirTransitionIdentity(usize),
    BadBoundaryConditionAuthenticationPaths,
    BadMerkleProof(MerkleProofError),
    LinearCombinationAuthenticationPath,
    LinearCombinationMismatch(usize), // integer refers to first index where a mismatch is found
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

// Return the interpolants for the provided points. This is the `L(x)` in the equation
// to derive the boundary quotient: `Q_B(x) = (ECT(x) - L(x)) / Z_B(x)`.
// input is indexed with bcs[register][cycle]
fn get_boundary_interpolants<'a>(
    bcs: Vec<Vec<(PrimeFieldElementBig<'a>, PrimeFieldElementBig<'a>)>>,
) -> Vec<Polynomial<PrimeFieldElementBig<'a>>> {
    bcs.iter()
        .map(|points| Polynomial::slow_lagrange_interpolation(points))
        .collect()
}

fn get_boundary_zerofiers<'a>(
    bcs: Vec<Vec<(PrimeFieldElementBig<'a>, PrimeFieldElementBig<'a>)>>,
) -> Vec<Polynomial<PrimeFieldElementBig<'a>>> {
    let roots: Vec<Vec<PrimeFieldElementBig>> = bcs
        .iter()
        .map(|points| points.iter().map(|(x, _y)| x.to_owned()).collect())
        .collect();
    roots
        .iter()
        .map(|points| Polynomial::get_polynomial_with_roots(points))
        .collect()
}

impl<'a> Stark<'a> {
    // Return the degrees of the boundary quotients
    fn boundary_quotient_degree_bounds(
        &self,
        boundary_zerofiers: &[Polynomial<PrimeFieldElementBig>],
    ) -> Vec<usize> {
        let transition_degree = self.randomized_trace_length - 1;
        boundary_zerofiers
            .iter()
            .map(|x| transition_degree - x.degree() as usize)
            .collect()
    }

    // Return the max degree for all interpolations of the execution trace
    fn transition_degree_bounds(
        &self,
        transition_constraints: &[MPolynomial<PrimeFieldElementBig>],
    ) -> Vec<usize> {
        let mut point_degrees = vec![0; 1 + 2 * self.register_count];
        point_degrees[0] = 1;
        for r in 0..self.register_count {
            point_degrees[1 + r] = self.randomized_trace_length - 1;
            point_degrees[1 + r + self.register_count] = self.randomized_trace_length - 1;
        }

        // This could also be achieved with symbolic evaluation of the
        // input `transition_constraints` and then taking the degree of
        // the resulting polynomials.
        let mut res: Vec<usize> = vec![];
        for a in transition_constraints {
            let mut max_degree = 0usize;
            for (k, _) in a.coefficients.iter() {
                let mut acc = 0;
                for (r, l) in point_degrees.iter().zip(k.iter()) {
                    acc += *r * (*l as usize);
                }
                if acc > max_degree {
                    max_degree = acc;
                }
            }
            res.push(max_degree);
        }

        res
    }

    /// Return the max degree for all transition quotients
    /// This is the degree of the execution trace interpolations
    /// divided by the transition zerofier polynomial
    fn transition_quotient_degree_bounds(
        &self,
        transition_constraints: &[MPolynomial<PrimeFieldElementBig>],
    ) -> Vec<usize> {
        // The degree is the degree of the trace plus the randomizers
        // minus the original trace length minus 1.
        self.transition_degree_bounds(transition_constraints)
            .iter()
            .map(|d| d - (self.original_trace_length - 1))
            .collect()
    }

    /// Return the degree of the combination polynomial, this is the degree limit,
    /// that is proven by FRI
    fn max_degree(&self, transition_constraints: &[MPolynomial<PrimeFieldElementBig>]) -> usize {
        let tqdbs: Vec<usize> = self.transition_quotient_degree_bounds(transition_constraints);
        let md_res = tqdbs.iter().max();
        let md = md_res.unwrap();
        // Round up to nearest 2^k - 1
        let l2 = log_2_ceil(*md as u64);
        (1 << l2) - 1
    }

    fn sample_weights(&'a self, randomness: &[u8], number: usize) -> Vec<PrimeFieldElementBig<'a>> {
        let k_seeds = utils::get_n_hash_rounds(randomness, number as u32);
        k_seeds
            .iter()
            .map(|seed| PrimeFieldElementBig::from_bytes(&self.field, seed))
            .collect::<Vec<PrimeFieldElementBig<'a>>>()
    }

    // Convert boundary constraints into a vector of boundary
    // constraints indexed by register.
    fn format_boundary_constraints(
        &self,
        boundary_constraints: Vec<BoundaryConstraint<'a>>,
    ) -> Vec<Vec<(PrimeFieldElementBig<'a>, PrimeFieldElementBig<'a>)>> {
        let mut bcs: Vec<Vec<(PrimeFieldElementBig, PrimeFieldElementBig)>> =
            vec![vec![]; self.register_count];
        for bc in boundary_constraints {
            bcs[bc.register].push((self.omicron.mod_pow(bc.cycle.into()), bc.value));
        }

        bcs
    }

    // Return a polynomial with roots along the entire trace except
    // the last point
    fn transition_zerofier(&self) -> Polynomial<PrimeFieldElementBig> {
        Polynomial::get_polynomial_with_roots(
            &self.omicron_domain[0..self.original_trace_length - 1],
        )
    }

    pub fn prove(
        &self,
        // Trace is indexed as trace[cycle][register]
        trace: Vec<Vec<PrimeFieldElementBig>>,
        transition_constraints: Vec<MPolynomial<PrimeFieldElementBig>>,
        boundary_constraints: Vec<BoundaryConstraint>,
        proof_stream: &mut ProofStream,
    ) -> Result<(), Box<dyn Error>> {
        // Concatenate randomizers
        // TODO: PCG ("permuted congrential generator") is not cryptographically secure; so exchange this for something else like Keccak/SHAKE256
        let mut rng = Pcg64::seed_from_u64(17);
        let mut rand_bytes = [0u8; 32];
        let mut randomized_trace: Vec<Vec<PrimeFieldElementBig>> = trace;
        for _ in 0..self.randomizer_count {
            randomized_trace.push(vec![]);
            for _ in 0..self.register_count {
                rng.fill_bytes(&mut rand_bytes);
                randomized_trace
                    .last_mut()
                    .unwrap()
                    .push(self.field.from_bytes(&rand_bytes));
            }
        }

        // Interpolate the trace to get a polynomial going through all
        // trace values
        let randomized_trace_domain: Vec<PrimeFieldElementBig> = self
            .field
            .get_generator_values(&self.omicron, randomized_trace.len());
        let mut trace_polynomials = vec![];
        for r in 0..self.register_count {
            trace_polynomials.push(Polynomial::slow_lagrange_interpolation_new(
                &randomized_trace_domain,
                &randomized_trace
                    .iter()
                    .map(|t| t[r].clone())
                    .collect::<Vec<PrimeFieldElementBig>>(),
            ));
        }

        // Subtract boundary interpolants and divide out boundary zerofiers
        let bcs_formatted = self.format_boundary_constraints(boundary_constraints);
        let boundary_interpolants: Vec<Polynomial<PrimeFieldElementBig>> =
            get_boundary_interpolants(bcs_formatted.clone());
        let boundary_zerofiers: Vec<Polynomial<PrimeFieldElementBig>> =
            get_boundary_zerofiers(bcs_formatted.clone());
        let mut boundary_quotients: Vec<Polynomial<PrimeFieldElementBig>> =
            vec![Polynomial::ring_zero(); self.register_count];
        for r in 0..self.register_count {
            let div_res = (trace_polynomials[r].clone() - boundary_interpolants[r].clone())
                .divide(boundary_zerofiers[r].clone());
            assert!(
                div_res.1.is_zero(),
                "Remainder must be zero when dividing out boundary zerofier"
            );
            boundary_quotients[r] = div_res.0;
        }

        // Commit to boundary quotients
        let fri_domain = self.fri.get_evaluation_domain(&self.field);
        let mut boundary_quotient_merkle_trees: Vec<MerkleTree<BigInt>> = vec![];
        // for r in 0..self.register_count {
        for bq in boundary_quotients.iter() {
            // TODO: Replace with NTT evaluation
            let boundary_quotient_codeword: Vec<BigInt> =
                fri_domain.iter().map(|x| bq.evaluate(x).value).collect();
            let bq_merkle_tree = MerkleTree::from_vec(&boundary_quotient_codeword);
            proof_stream.enqueue(&bq_merkle_tree.get_root())?;
            boundary_quotient_merkle_trees.push(bq_merkle_tree);
        }

        // Symbolically evaluate transition constraints
        let x = Polynomial {
            coefficients: vec![self.omega.ring_zero(), self.omega.ring_one()],
        };
        let mut point: Vec<Polynomial<PrimeFieldElementBig>> = vec![x.clone()];

        // add polynomial representing trace[x_i] and trace[x_{i+1}]
        point.append(&mut trace_polynomials.clone());
        point.append(
            &mut trace_polynomials
                .clone() // TODO: REMOVE
                .into_iter()
                .map(|tp| tp.scale(&self.omicron))
                .collect(),
        );
        let transition_polynomials: Vec<Polynomial<PrimeFieldElementBig>> = transition_constraints
            .iter()
            .map(|x| x.evaluate_symbolic(&point))
            .collect();

        // divide out transition zerofier
        let mut transition_quotients: Vec<Polynomial<PrimeFieldElementBig>> =
            vec![Polynomial::ring_zero(); self.register_count];
        let transition_zerofier = self.transition_zerofier();
        for r in 0..self.register_count {
            let div_res = transition_polynomials[r].divide(transition_zerofier.clone());
            assert!(
                div_res.1.is_zero(),
                "Remainder must be zero when dividing out transition zerofier"
            );
            transition_quotients[r] = div_res.0;
        }

        // Commit to randomizer polynomial
        let max_degree = self.max_degree(&transition_constraints);
        let mut randomizer_polynomial_coefficients: Vec<PrimeFieldElementBig> = vec![];
        for _ in 0..max_degree + 1 {
            let mut rand_bytes = [0u8; 32];
            rng.fill_bytes(&mut rand_bytes);
            randomizer_polynomial_coefficients.push(self.field.from_bytes(&rand_bytes));
        }

        let randomizer_polynomial = Polynomial {
            coefficients: randomizer_polynomial_coefficients,
        };

        let randomizer_codeword: Vec<BigInt> = fri_domain
            .iter()
            .map(|x| randomizer_polynomial.evaluate(x).value)
            .collect();
        let randomizer_mt = MerkleTree::from_vec(&randomizer_codeword);
        proof_stream.enqueue(&randomizer_mt.get_root())?;

        // Sanity check, should probably be removed
        let expected_tq_degrees = self.transition_quotient_degree_bounds(&transition_constraints);
        for r in 0..self.register_count {
            assert_eq!(
                expected_tq_degrees[r] as isize,
                transition_quotients[r].degree(),
                "Transition quotient degree must match expected value"
            );
        }

        // Compute terms of nonlinear combination polynomial
        let boundary_degrees = self.boundary_quotient_degree_bounds(&boundary_zerofiers);
        let mut terms: Vec<Polynomial<PrimeFieldElementBig>> = vec![randomizer_polynomial];
        for (tq, tq_degree) in transition_quotients.iter().zip(expected_tq_degrees.iter()) {
            terms.push(tq.to_owned());
            let shift = max_degree - tq_degree;
            let shifted = tq.shift_coefficients(shift, self.omega.ring_zero());
            assert_eq!(max_degree as isize, shifted.degree()); // TODO: Can be removed
            terms.push(shifted);
        }
        for (bq, bq_degree) in boundary_quotients.iter().zip(boundary_degrees.iter()) {
            terms.push(bq.to_owned());
            let shift = max_degree - bq_degree;
            let shifted = bq.shift_coefficients(shift, self.omega.ring_zero());
            assert_eq!(max_degree as isize, shifted.degree()); // TODO: Can be removed
            terms.push(shifted);
        }

        // Take weighted sum
        // # get weights for nonlinear combination
        // #  - 1 randomizer
        // #  - 2 for every transition quotient
        // #  - 2 for every boundary quotient
        let fiat_shamir_hash: Vec<u8> = proof_stream.prover_fiat_shamir();
        let weights = self.sample_weights(
            &fiat_shamir_hash,
            1 + 2 * transition_quotients.len() + 2 * boundary_quotients.len(),
        );
        assert_eq!(
            weights.len(),
            terms.len(),
            "weights and terms length must match"
        );
        let combination = weights
            .iter()
            .zip(terms.iter())
            .fold(Polynomial::ring_zero(), |sum, (weight, pol)| {
                sum + pol.scalar_mul(weight.to_owned())
            });

        let mut combined_codeword = vec![];
        for point in fri_domain.iter() {
            combined_codeword.push(combination.evaluate(point));
        }

        // Prove low degree of combination polynomial, and collect indices
        let indices: Vec<usize> = self.fri.prove(
            &combined_codeword
                .iter()
                .map(|x| x.value.clone())
                .collect::<Vec<BigInt>>(),
            proof_stream,
        )?;

        // Process indices
        let mut duplicated_indices = indices.clone();
        duplicated_indices.append(
            &mut indices
                .into_iter()
                .map(|i| (i + self.expansion_factor) % self.fri.domain_length)
                .collect(),
        );
        let mut quadrupled_indices = duplicated_indices.clone();
        quadrupled_indices.append(
            &mut duplicated_indices
                .into_iter()
                .map(|i| (i + self.fri.domain_length / 2) % self.fri.domain_length)
                .collect(),
        );
        quadrupled_indices.sort_unstable();

        // Open indicated positions in the boundary quotient codewords
        for bq_mt in boundary_quotient_merkle_trees {
            proof_stream.enqueue_length_prepended(&bq_mt.get_multi_proof(&quadrupled_indices))?;
        }

        // Open indicated positions in the randomizer
        proof_stream
            .enqueue_length_prepended(&randomizer_mt.get_multi_proof(&quadrupled_indices))?;

        Ok(())
    }

    pub fn verify(
        &self,
        proof_stream: &mut ProofStream,
        transition_constraints: Vec<MPolynomial<PrimeFieldElementBig>>,
        boundary_constraints: Vec<BoundaryConstraint>,
    ) -> Result<(), Box<dyn Error>> {
        // Get Merkle root of boundary quotient codewords
        let mut boundary_quotient_mt_roots: Vec<[u8; 32]> = vec![];
        for _ in 0..self.register_count {
            boundary_quotient_mt_roots.push(proof_stream.dequeue(32)?);
        }

        let randomizer_mt_root: [u8; 32] = proof_stream.dequeue(32)?;

        // Get weights for nonlinear combination
        // 1 weight element for randomizer
        // 2 for every transition quotient
        // 2 for every boundary quotient
        let fiat_shamir_hash: Vec<u8> = proof_stream.verifier_fiat_shamir();
        let weights = self.sample_weights(
            &fiat_shamir_hash,
            1 + 2 * boundary_quotient_mt_roots.len() + 2 * transition_constraints.len(),
        );

        // Verify low degree of combination polynomial, and collect indices
        // Note that FRI verifier verifies number of samples, so we don't have
        // to check that number here
        let polynomial_values = self.fri.verify(proof_stream)?;

        let indices: Vec<usize> = polynomial_values.iter().map(|(i, _y)| *i).collect();
        let values: Vec<BigInt> = polynomial_values.iter().map(|(_i, y)| y.clone()).collect();

        let mut duplicated_indices = indices.clone();
        duplicated_indices.append(
            &mut indices
                .iter()
                .map(|i| (*i + self.expansion_factor) % self.fri.domain_length)
                .collect(),
        );
        duplicated_indices.sort_unstable();

        // Read and verify boundary quotient leafs
        // revealed boundary quotient codeword values, indexed by (register, codeword index)
        let mut boundary_quotients: Vec<HashMap<usize, PrimeFieldElementBig>> = vec![];
        for (i, bq_root) in boundary_quotient_mt_roots.into_iter().enumerate() {
            boundary_quotients.push(HashMap::new());
            let authentication_paths: Vec<PartialAuthenticationPath<BigInt>> =
                proof_stream.dequeue_length_prepended()?;
            let valid =
                MerkleTree::verify_multi_proof(bq_root, &duplicated_indices, &authentication_paths);
            if !valid {
                return Err(Box::new(StarkVerifyError::BadMerkleProof(
                    MerkleProofError::BoundaryQuotientError(i),
                )));
            }

            duplicated_indices
                .iter()
                .zip(authentication_paths.iter())
                .for_each(|(index, authentication_path)| {
                    boundary_quotients[i].insert(
                        *index,
                        PrimeFieldElementBig::new(authentication_path.get_value(), &self.field),
                    );
                });
        }

        // Read and verify randomizer leafs
        let authentication_paths: Vec<PartialAuthenticationPath<BigInt>> =
            proof_stream.dequeue_length_prepended()?;
        let valid = MerkleTree::verify_multi_proof(
            randomizer_mt_root,
            &duplicated_indices,
            &authentication_paths,
        );
        if !valid {
            return Err(Box::new(StarkVerifyError::BadMerkleProof(
                MerkleProofError::RandomizerError,
            )));
        }

        let mut randomizer_values: HashMap<usize, PrimeFieldElementBig> = HashMap::new();
        duplicated_indices
            .iter()
            .zip(authentication_paths.iter())
            .for_each(|(index, authentication_path)| {
                randomizer_values.insert(
                    *index,
                    PrimeFieldElementBig::new(authentication_path.get_value(), &self.field),
                );
            });

        // Verify leafs of combination polynomial
        let formatted_bcs = self.format_boundary_constraints(boundary_constraints);
        let boundary_zerofiers = get_boundary_zerofiers(formatted_bcs.clone());
        let boundary_interpolants = get_boundary_interpolants(formatted_bcs);
        let transition_zerofier = self.transition_zerofier();
        let max_degree = self.max_degree(&transition_constraints);
        let boundary_degrees = self.boundary_quotient_degree_bounds(&boundary_zerofiers);
        let expected_tq_degrees = self.transition_quotient_degree_bounds(&transition_constraints);
        for (i, current_index) in indices.into_iter().enumerate() {
            let current_x: PrimeFieldElementBig =
                self.field_generator.clone() * self.omega.mod_pow(current_index.into());
            let next_index: usize =
                (current_index + self.expansion_factor) % self.fri.domain_length;
            let next_x: PrimeFieldElementBig =
                self.field_generator.clone() * self.omega.mod_pow(next_index.into());
            let mut current_trace: Vec<PrimeFieldElementBig> = (0..self.register_count)
                .map(|r| {
                    boundary_quotients[r][&current_index].clone()
                        * boundary_zerofiers[r].evaluate(&current_x)
                        + boundary_interpolants[r].evaluate(&current_x)
                })
                .collect();
            let mut next_trace: Vec<PrimeFieldElementBig> = (0..self.register_count)
                .map(|r| {
                    boundary_quotients[r][&next_index].clone()
                        * boundary_zerofiers[r].evaluate(&next_x)
                        + boundary_interpolants[r].evaluate(&next_x)
                })
                .collect();

            let mut point: Vec<PrimeFieldElementBig> = vec![current_x.clone()];
            point.append(&mut current_trace);
            point.append(&mut next_trace);

            let transition_constraint_values: Vec<PrimeFieldElementBig> = transition_constraints
                .iter()
                .map(|tc| tc.evaluate(&point))
                .collect();

            // Get combination polynomial evaluation value
            // Loop over all registers for transition quotient values, and for boundary quotient values
            let mut terms: Vec<PrimeFieldElementBig> =
                vec![randomizer_values[&current_index].clone()];
            for (tcv, tq_degree) in transition_constraint_values
                .iter()
                .zip(expected_tq_degrees.iter())
            {
                let transition_quotient = tcv.to_owned() / transition_zerofier.evaluate(&current_x);
                terms.push(transition_quotient.clone());
                let shift = max_degree - tq_degree;
                terms.push(transition_quotient * current_x.mod_pow(shift.into()));
            }
            for (bqvs, bq_degree) in boundary_quotients.iter().zip(boundary_degrees.iter()) {
                terms.push(bqvs[&current_index].clone());
                let shift = max_degree - bq_degree;
                terms.push(bqvs[&current_index].clone() * current_x.mod_pow(shift.into()));
            }

            assert_eq!(
                weights.len(),
                terms.len(),
                "weights and terms length must match in verifier"
            );
            let combination = weights
                .iter()
                .zip(terms.iter())
                .fold(self.omega.ring_zero(), |sum, (weight, term)| {
                    sum + term.to_owned() * weight.to_owned()
                });

            if values[i] != combination.value {
                return Err(Box::new(StarkVerifyError::LinearCombinationMismatch(
                    current_index,
                )));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod test_slow_stark {
    use num_bigint::BigInt;

    use crate::shared_math::rescue_prime_stark::RescuePrime;

    use super::*;

    pub fn get_tutorial_stark<'a>(field: &'a PrimeFieldBig) -> (Stark<'a>, RescuePrime<'a>) {
        let expansion_factor = 4;
        let colinearity_checks_count = 2;
        let rescue_prime = RescuePrime::from_tutorial(&field);
        let register_count = rescue_prime.m;
        let cycles_count = rescue_prime.steps_count + 1;
        let transition_constraints_degree = 2;
        let generator =
            PrimeFieldElementBig::new(85408008396924667383611388730472331217u128.into(), &field);

        (
            Stark::new(
                &field,
                expansion_factor,
                colinearity_checks_count,
                register_count,
                cycles_count,
                transition_constraints_degree,
                generator,
            ),
            rescue_prime,
        )
    }

    #[test]
    fn prng_with_seed() {
        let mut rng = Pcg64::seed_from_u64(2);
        let mut rand_bytes = [0u8; 32];
        rng.fill_bytes(&mut rand_bytes);

        let modulus: BigInt = (407u128 * (1 << 119) + 1).into();
        let field = PrimeFieldBig::new(modulus);
        let fe = field.from_bytes(&rand_bytes);
        println!("fe = {}", fe);
        let expected: BigInt = 114876749706552506467803119432194128310u128.into();
        assert_eq!(expected, fe.value);
    }

    #[test]
    fn boundary_quotient_degree_bounds_test() {
        let modulus: BigInt = (407u128 * (1 << 119) + 1).into();
        let field = PrimeFieldBig::new(modulus);
        let (stark, rescue_prime) = get_tutorial_stark(&field);
        let input = PrimeFieldElementBig::new(228894434762048332457318u128.into(), &field);
        let output_element = rescue_prime.hash(&input);
        let boundary_constraints = rescue_prime.get_boundary_constraints(&output_element);
        let bcs_formatted = stark.format_boundary_constraints(boundary_constraints);
        let boundary_zerofiers: Vec<Polynomial<PrimeFieldElementBig>> =
            get_boundary_zerofiers(bcs_formatted.clone());
        let degrees = stark.boundary_quotient_degree_bounds(&boundary_zerofiers);
        assert_eq!(vec![34, 34], degrees);
    }

    #[test]
    fn max_degree_test() {
        let modulus: BigInt = (407u128 * (1 << 119) + 1).into();
        let field = PrimeFieldBig::new(modulus);
        let (stark, rescue_prime) = get_tutorial_stark(&field);
        let res = stark.max_degree(&rescue_prime.get_air_constraints(&stark.omicron));
        assert_eq!(127usize, res);
    }

    #[test]
    fn transition_quotient_degree_bounds_test() {
        let modulus: BigInt = (407u128 * (1 << 119) + 1).into();
        let field = PrimeFieldBig::new(modulus);
        let (stark, rescue_prime) = get_tutorial_stark(&field);
        let res = stark
            .transition_quotient_degree_bounds(&rescue_prime.get_air_constraints(&stark.omicron));
        // tq.degree()
        // = ((rp.step_count + num_randomizer )* air_constraints.degree()) - transition_zerofier.degree()
        // = (27 + 8) * 3 - 27 = 78
        assert_eq!(vec![78, 78], res);
    }

    #[test]
    fn transition_degree_bounds_test() {
        let modulus: BigInt = (407u128 * (1 << 119) + 1).into();
        let field = PrimeFieldBig::new(modulus);
        let (stark, rescue_prime) = get_tutorial_stark(&field);
        let res = stark.transition_degree_bounds(&rescue_prime.get_air_constraints(&stark.omicron));
        assert_eq!(vec![105, 105], res);
    }

    #[test]
    fn rescue_prime_stark() {
        let modulus: BigInt = (407u128 * (1 << 119) + 1).into();
        let field = PrimeFieldBig::new(modulus);
        let (stark, rescue_prime) = get_tutorial_stark(&field);

        let input = PrimeFieldElementBig::new(228894434762048332457318u128.into(), &field);
        let trace = rescue_prime.trace(&input);
        let output_element = trace[rescue_prime.steps_count][0].clone();
        let transition_constraints = rescue_prime.get_air_constraints(&stark.omicron);
        let boundary_constraints = rescue_prime.get_boundary_constraints(&output_element);
        let mut proof_stream = ProofStream::default();

        let stark_proof = stark.prove(
            trace,
            transition_constraints.clone(),
            boundary_constraints.clone(),
            &mut proof_stream,
        );
        match stark_proof {
            Ok(()) => (),
            Err(_) => panic!("Failed to produce STARK proof."),
        }
        let verify = stark.verify(
            &mut proof_stream,
            transition_constraints,
            boundary_constraints,
        );
        match verify {
            Ok(_) => (),
            Err(err) => panic!("Verification of STARK proof failed with error: {}", err),
        };
    }
}
