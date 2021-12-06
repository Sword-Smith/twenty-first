use std::{error::Error, fmt};

use num_bigint::BigInt;
use num_traits::Zero;

use crate::shared_math::polynomial::Polynomial;
use crate::util_types::merkle_tree::PartialAuthenticationPath;
use crate::util_types::{merkle_tree::MerkleTree, proof_stream::ProofStream};
use crate::utils::{blake3_digest, get_index_from_bytes};

use super::ntt::intt;
use super::{
    other::log_2_ceil,
    prime_field_element_big::{PrimeFieldBig, PrimeFieldElementBig},
};

#[derive(Debug, Eq, PartialEq)]
pub enum ProveError {
    BadMaxDegreeValue,
    NonPostiveRoundCount,
}

impl Error for ProveError {}

impl fmt::Display for ProveError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Deserialization error for LowDegreeProof: {:?}", self)
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum ValidationError {
    BadMerkleProof,
    BadSizedProof,
    NonPostiveRoundCount,
    NotColinear(usize),
    LastIterationTooHighDegree,
    BadMerkleRootForLastCodeword,
}

impl Error for ValidationError {}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Deserialization error for LowDegreeProof: {:?}", self)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Fri {
    offset: BigInt,           // use generator for offset
    omega: BigInt,            // generator of the expanded domain
    pub domain_length: usize, // after expansion
    modulus: BigInt,
    expansion_factor: usize, // expansion_factor = fri_domain_length / trace_length
    colinearity_checks_count: usize,
}

impl Fri {
    // Return the c-indices for the 1st round of FRI
    fn sample_indices(&self, seed: &[u8]) -> Vec<usize> {
        let snd_codeword_length = self.domain_length / 2;
        let last_codeword_len = snd_codeword_length >> (self.num_rounds().0 - 1);
        assert!(
            self.colinearity_checks_count <= last_codeword_len,
            "Requested number of indices must not exceed length of last codeword"
        );
        assert!(
            self.colinearity_checks_count <= 2 * last_codeword_len,
            "Not enough entropy in indices wrt last codeword"
        );

        let mut indices: Vec<usize> = vec![];
        let mut reduced_indices: Vec<usize> = vec![];
        let mut counter = 0u32;
        while indices.len() < self.colinearity_checks_count {
            let mut seed_local: Vec<u8> = seed.to_vec();
            seed_local.append(&mut counter.to_be_bytes().into());
            let hash = blake3_digest(seed_local.as_slice());
            let index = get_index_from_bytes(&hash, snd_codeword_length);
            let reduced_index = index % last_codeword_len;
            counter += 1;
            if !reduced_indices.contains(&reduced_index) {
                indices.push(index);
                reduced_indices.push(reduced_index);
            }
        }

        indices
    }

    fn commit(
        &self,
        codeword: &[BigInt],
        proof_stream: &mut ProofStream,
    ) -> Result<Vec<MerkleTree<BigInt>>, Box<dyn Error>> {
        let mut generator = self.omega.clone();
        let mut offset = self.offset.clone();
        let mut codeword_local = codeword.to_vec();
        let one: BigInt = 1.into();
        let two: BigInt = 2.into();
        let (_, two_inv_res, _) = PrimeFieldElementBig::eea(two.clone(), self.modulus.clone());

        // Ensure that 2^(-1) > 0 as eea may return negative values
        let two_inv = (two_inv_res + self.modulus.clone()) % self.modulus.clone();

        assert!(
            two_inv.clone() * two % self.modulus.clone() == one,
            "2^(-1) * 2 must equal 1"
        ); // TODO: REMOVE

        // Compute and send Merkle root
        let mut mt = MerkleTree::from_vec(&codeword_local);
        proof_stream.enqueue(&mt.get_root())?;
        let mut merkle_trees = vec![mt];

        let (num_rounds, _) = self.num_rounds();
        let field = PrimeFieldBig::new(self.modulus.clone());
        for _ in 0..num_rounds {
            let n = codeword_local.len();

            // Sanity check to verify that generator has the right order
            let generator_fe = PrimeFieldElementBig::new(generator.clone(), &field);
            assert!(generator_fe.inv() == generator_fe.mod_pow((n - 1).into())); // TODO: REMOVE

            // Get challenge
            let alpha = field.from_bytes(&proof_stream.prover_fiat_shamir()).value;

            let x_offset: Vec<BigInt> = field
                .get_power_series(generator.clone())
                .iter()
                .map(|x| x * offset.clone() % self.modulus.clone())
                .collect();
            let x_offset_inverses = field.batch_inversion(x_offset.clone());
            for i in 0..n / 2 {
                codeword_local[i] = ((two_inv.clone()
                    * ((one.clone() + alpha.clone() * x_offset_inverses[i].clone())
                        * codeword_local[i].clone()
                        + (one.clone() - alpha.clone() * x_offset_inverses[i].clone())
                            * codeword_local[n / 2 + i].clone()))
                    % self.modulus.clone()
                    + self.modulus.clone())
                    % self.modulus.clone();
            }
            codeword_local.resize(n / 2, BigInt::zero());

            // Compute and send Merkle root
            mt = MerkleTree::from_vec(&codeword_local);
            proof_stream.enqueue(&mt.get_root())?;
            merkle_trees.push(mt);

            // Update subgroup generator and offset
            generator = generator.clone() * generator.clone() % self.modulus.clone();
            offset = offset.clone() * offset.clone() % self.modulus.clone();
        }

        // Send the last codeword
        proof_stream.enqueue_length_prepended(&codeword_local)?;

        Ok(merkle_trees)
    }

    // Find number of rounds from max_degree. If expansion factor is less than the security level (s),
    // then we need to stop the iteration when the remaining codeword (that is halved in each round)
    // has a length smaller than the security level. Otherwise, we couldn't test enough points for the
    // remaining code word.
    // codeword_size *should* be a multiple of `max_degree + 1`
    // rounds_count is the number of times the code word length is halved
    // In reality we demain that the length of the last codeword i 2 times the number of colinearity
    // checks, as this makes index picking easier.
    fn num_rounds(&self) -> (u8, u32) {
        let max_degree = (self.domain_length / self.expansion_factor) - 1;
        let mut rounds_count = log_2_ceil(max_degree as u64 + 1) as u8;
        let mut max_degree_of_last_round = 0u32;
        if self.expansion_factor < 2 * self.colinearity_checks_count {
            let num_missed_rounds = log_2_ceil(
                (2f64 * self.colinearity_checks_count as f64 / self.expansion_factor as f64).ceil()
                    as u64,
            ) as u8;
            rounds_count -= num_missed_rounds;
            max_degree_of_last_round = 2u32.pow(num_missed_rounds as u32) - 1;
        }

        (rounds_count, max_degree_of_last_round)
    }

    pub fn new(
        offset: BigInt,
        omega: BigInt,
        initial_domain_length: usize,
        expansion_factor: usize,
        colinearity_check_count: usize,
        modulus: BigInt,
    ) -> Self {
        Self {
            modulus,
            colinearity_checks_count: colinearity_check_count,
            domain_length: initial_domain_length,
            expansion_factor,
            offset,
            omega,
        }
    }

    pub fn get_evaluation_domain<'a>(
        &self,
        field: &'a PrimeFieldBig,
    ) -> Vec<PrimeFieldElementBig<'a>> {
        let omega_fe = PrimeFieldElementBig::new(self.omega.clone(), field);
        let offset_fe = PrimeFieldElementBig::new(self.offset.clone(), field);
        let omega_domain = omega_fe.get_generator_domain();
        omega_domain
            .into_iter()
            .map(|x| x * offset_fe.clone())
            .collect()
    }

    fn query(
        &self,
        current_mt: MerkleTree<BigInt>,
        next_mt: MerkleTree<BigInt>,
        c_indices: &[usize],
        proof_stream: &mut ProofStream,
    ) -> Result<(), Box<dyn Error>> {
        let a_indices: Vec<usize> = c_indices.to_vec();
        let mut b_indices: Vec<usize> = c_indices
            .iter()
            .map(|x| x + current_mt.get_number_of_leafs() / 2)
            .collect();
        let mut ab_indices = a_indices;
        ab_indices.append(&mut b_indices);

        // Reveal authentication paths
        proof_stream.enqueue_length_prepended(&current_mt.get_multi_proof(&ab_indices))?;
        proof_stream.enqueue_length_prepended(&next_mt.get_multi_proof(c_indices))?;

        Ok(())
    }

    pub fn prove(
        &self,
        codeword: &[BigInt],
        proof_stream: &mut ProofStream,
    ) -> Result<Vec<usize>, Box<dyn Error>> {
        assert_eq!(
            self.domain_length,
            codeword.len(),
            "Initial codeword length must match that set in FRI object"
        );

        // Commit phase
        let merkle_trees: Vec<MerkleTree<BigInt>> = self.commit(codeword, proof_stream)?;
        let codewords: Vec<Vec<BigInt>> = merkle_trees.iter().map(|x| x.to_vec()).collect();

        // fiat-shamir phase (get indices)
        let top_level_indices = self.sample_indices(&proof_stream.prover_fiat_shamir());

        // query phase
        let mut c_indices = top_level_indices.clone();
        for i in 0..merkle_trees.len() - 1 {
            c_indices = c_indices
                .clone()
                .iter()
                .map(|x| x % (codewords[i].len() / 2))
                .collect();
            self.query(
                merkle_trees[i].clone(),
                merkle_trees[i + 1].clone(),
                &c_indices,
                proof_stream,
            )?;
        }

        Ok(top_level_indices)
    }

    // Verify a FRI proof. Returns evaluated points from the 1st FRI iteration.
    pub fn verify(
        &self,
        proof_stream: &mut ProofStream,
    ) -> Result<Vec<(usize, BigInt)>, Box<dyn Error>> {
        let field = PrimeFieldBig::new(self.modulus.clone());
        let omega = self.omega.clone();
        let mut omega_fe = PrimeFieldElementBig::new(omega, &field);
        let offset = self.offset.clone();
        let mut offset_fe = PrimeFieldElementBig::new(offset, &field);
        let (num_rounds, degree_of_last_round) = self.num_rounds();

        // Extract all roots and calculate alpha, the challenges
        let mut roots: Vec<[u8; 32]> = vec![];
        let mut alphas = vec![];
        roots.push(proof_stream.dequeue::<[u8; 32]>(32)?);
        for _ in 0..num_rounds {
            alphas.push(field.from_bytes(&proof_stream.verifier_fiat_shamir()));
            roots.push(proof_stream.dequeue::<[u8; 32]>(32)?);
        }

        // Extract last codeword
        let last_codeword: Vec<BigInt> = proof_stream.dequeue_length_prepended::<Vec<BigInt>>()?;

        // Check if last codeword matches the given root
        if *roots.last().unwrap() != MerkleTree::from_vec(&last_codeword).get_root() {
            return Err(Box::new(ValidationError::BadMerkleRootForLastCodeword));
        }

        // Verify that last codeword is of sufficiently low degree
        let mut last_omega_fe = omega_fe.clone();
        let mut last_offset_fe = offset_fe.clone();
        for _ in 0..num_rounds {
            last_omega_fe = last_omega_fe.mod_pow(2.into());
            last_offset_fe = last_offset_fe.mod_pow(2.into());
        }

        // Compute interpolant to get the degree of the last codeword
        // Note that we don't have to scale the polynomial back to the
        // trace subgroup since we only check its degree and don't use
        // it further.
        let last_codeword_fes: Vec<PrimeFieldElementBig> = last_codeword
            .iter()
            .map(|x| PrimeFieldElementBig::new(x.clone(), &field))
            .collect();
        let coefficients = intt(&last_codeword_fes, &last_omega_fe);
        let last_poly_degree: isize = (Polynomial { coefficients }).degree();
        if last_poly_degree > degree_of_last_round as isize {
            return Err(Box::new(ValidationError::LastIterationTooHighDegree));
        }

        let top_level_indices = self.sample_indices(&proof_stream.verifier_fiat_shamir());

        // for every round, check consistency of subsequent layers
        let mut codeword_evaluations: Vec<(usize, BigInt)> = vec![];
        for r in 0..num_rounds as usize {
            // Fold c indices
            let c_indices: Vec<usize> = top_level_indices
                .iter()
                .map(|x| x % (self.domain_length >> (r + 1)))
                .collect();

            // Infer a and b indices
            let a_indices = c_indices.clone();
            let b_indices: Vec<usize> = a_indices
                .iter()
                .map(|x| x + (self.domain_length >> (r + 1)))
                .collect();
            let mut ab_indices: Vec<usize> = a_indices.clone();
            ab_indices.append(&mut b_indices.clone());

            // Read values and check colinearity
            let ab_values: Vec<PartialAuthenticationPath<BigInt>> =
                proof_stream.dequeue_length_prepended()?;
            let c_values: Vec<PartialAuthenticationPath<BigInt>> =
                proof_stream.dequeue_length_prepended()?;

            // verify Merkle authentication paths
            if !MerkleTree::verify_multi_proof(roots[r], &ab_indices, &ab_values)
                || !MerkleTree::verify_multi_proof(roots[r + 1], &c_indices, &c_values)
            {
                return Err(Box::new(ValidationError::BadMerkleProof));
            }

            // Verify that the expected number of samples are present
            if ab_values.len() != 2 * self.colinearity_checks_count
                || c_values.len() != self.colinearity_checks_count
            {
                return Err(Box::new(ValidationError::BadSizedProof));
            }

            // Colinearity check
            let axs: Vec<PrimeFieldElementBig> = (0..self.colinearity_checks_count)
                .map(|i| offset_fe.clone() * omega_fe.clone().mod_pow(a_indices[i].into()))
                .collect();
            let bxs: Vec<PrimeFieldElementBig> = (0..self.colinearity_checks_count)
                .map(|i| offset_fe.clone() * omega_fe.clone().mod_pow(b_indices[i].into()))
                .collect();
            let cx: PrimeFieldElementBig = alphas[r].clone();
            let ays: Vec<PrimeFieldElementBig> = (0..self.colinearity_checks_count)
                .map(|i| ab_values[i].get_value())
                .map(|y| PrimeFieldElementBig::new(y, &field))
                .collect();
            let bys: Vec<PrimeFieldElementBig> = (0..self.colinearity_checks_count)
                .map(|i| ab_values[i + self.colinearity_checks_count].get_value())
                .map(|y| PrimeFieldElementBig::new(y, &field))
                .collect();
            let cys: Vec<PrimeFieldElementBig> = (0..self.colinearity_checks_count)
                .map(|i| c_values[i].get_value())
                .map(|y| PrimeFieldElementBig::new(y, &field))
                .collect();

            if (0..self.colinearity_checks_count).any(|i| {
                !Polynomial::are_colinear(&[
                    (axs[i].clone(), ays[i].clone()),
                    (bxs[i].clone(), bys[i].clone()),
                    (cx.clone(), cys[i].clone()),
                ])
            }) {
                return Err(Box::new(ValidationError::NotColinear(r)));
            }
            // Update subgroup generator and offset
            omega_fe = omega_fe.clone() * omega_fe.clone();
            offset_fe = offset_fe.clone() * offset_fe.clone();

            // Return top-level values to caller
            if r == 0 {
                for s in 0..self.colinearity_checks_count {
                    codeword_evaluations.push((a_indices[s], ays[s].value.clone()));
                    codeword_evaluations.push((b_indices[s], bys[s].value.clone()));
                }
            }
        }

        Ok(codeword_evaluations)
    }
}

#[cfg(test)]
mod test_fri {
    use crate::shared_math::polynomial::Polynomial;

    use super::*;

    #[allow(clippy::needless_lifetimes)] // Suppress wrong warning (fails to compile without lifetime, I think)
    fn pfb<'a>(value: BigInt, field: &'a PrimeFieldBig) -> PrimeFieldElementBig {
        PrimeFieldElementBig::new(value, field)
    }

    fn get_fri_test_object() -> Fri {
        let modulus: BigInt = (407u128 * (1 << 119) + 1).into();
        // 512th root of the prime field
        let omega: BigInt = 11068365217297290165464327737828832066u128.into();
        let generator: BigInt = 85408008396924667383611388730472331217u128.into();
        let expansion_factor = 4usize;
        let colinearity_checks_count = 2usize;
        let initial_domain_length = 512usize;
        Fri::new(
            generator,
            omega,
            initial_domain_length,
            expansion_factor,
            colinearity_checks_count,
            modulus,
        )
    }

    #[test]
    fn get_rounds_count_test() {
        let mut fri = get_fri_test_object();
        assert_eq!((7, 0), fri.num_rounds());
        fri.colinearity_checks_count = 8;
        assert_eq!((5, 3), fri.num_rounds());
        fri.colinearity_checks_count = 10;
        assert_eq!((4, 7), fri.num_rounds());
        fri.colinearity_checks_count = 16;
        assert_eq!((4, 7), fri.num_rounds());
        fri.colinearity_checks_count = 17;
        assert_eq!((3, 15), fri.num_rounds());
        fri.colinearity_checks_count = 18;
        assert_eq!((3, 15), fri.num_rounds());
        fri.colinearity_checks_count = 31;
        assert_eq!((3, 15), fri.num_rounds());
        fri.colinearity_checks_count = 32;
        assert_eq!((3, 15), fri.num_rounds());
        fri.colinearity_checks_count = 33;
        assert_eq!((2, 31), fri.num_rounds());

        fri.domain_length = 256;
        assert_eq!((1, 31), fri.num_rounds());
        fri.colinearity_checks_count = 32;
        assert_eq!((2, 15), fri.num_rounds());

        fri.colinearity_checks_count = 32;
        fri.domain_length = 1048576;
        fri.expansion_factor = 8;
        assert_eq!((14, 7), fri.num_rounds());

        fri.colinearity_checks_count = 33;
        fri.domain_length = 1048576;
        fri.expansion_factor = 8;
        assert_eq!((13, 15), fri.num_rounds());

        fri.colinearity_checks_count = 63;
        fri.domain_length = 1048576;
        fri.expansion_factor = 8;
        assert_eq!((13, 15), fri.num_rounds());

        fri.colinearity_checks_count = 64;
        fri.domain_length = 1048576;
        fri.expansion_factor = 8;
        assert_eq!((13, 15), fri.num_rounds());

        fri.colinearity_checks_count = 65;
        fri.domain_length = 1048576;
        fri.expansion_factor = 8;
        assert_eq!((12, 31), fri.num_rounds());

        fri.domain_length = 256;
        fri.expansion_factor = 4;
        fri.colinearity_checks_count = 17;
        assert_eq!((2, 15), fri.num_rounds());
    }

    #[test]
    fn generate_proof_small_bigint() {
        let mut ret: Option<(PrimeFieldBig, BigInt)> = None;
        PrimeFieldBig::get_field_with_primitive_root_of_unity(4, 200, &mut ret);
        assert_eq!(Into::<BigInt>::into(229i128), ret.clone().unwrap().0.q);
        let (field, primitive_root_of_unity) = ret.clone().unwrap();
        let power_series = field.get_power_series(primitive_root_of_unity.clone());
        assert_eq!(4, power_series.len());
        assert_eq!(
            vec![
                Into::<BigInt>::into(1i128),
                Into::<BigInt>::into(122),
                Into::<BigInt>::into(228),
                Into::<BigInt>::into(107)
            ],
            power_series
        );
        let generator: BigInt = 7.into();
        let field_elements = field.get_power_series(generator.clone());
        assert_eq!(228, field_elements.len());

        let fri = Fri::new(generator, primitive_root_of_unity, 4, 2, 1, 229.into());
        let mut proof_stream: ProofStream = ProofStream::default();
        fri.prove(&power_series, &mut proof_stream).unwrap();

        let verify_result = fri.verify(&mut proof_stream);
        assert!(verify_result.is_ok(), "FRI verification must succeed");
    }

    #[test]
    fn generate_proof_cubica_bigint() {
        let mut ret: Option<(PrimeFieldBig, BigInt)> = None;
        PrimeFieldBig::get_field_with_primitive_root_of_unity(16, 10000, &mut ret);
        let (field, primitive_root_of_unity_bi) = ret.clone().unwrap();
        assert_eq!(Into::<BigInt>::into(10177), field.q);
        let field_generator: BigInt = 7.into(); // 7 was verified to be a generator of F_{10177}
        let domain: Vec<BigInt> = field.get_power_series(primitive_root_of_unity_bi.clone());
        let pol = Polynomial {
            coefficients: vec![
                pfb(6.into(), &field),
                pfb(14.into(), &field),
                pfb(2.into(), &field),
                pfb(5.into(), &field),
            ],
        };
        let mut y_values = domain
            .clone()
            .into_iter()
            .map(|x| pol.evaluate(&pfb(x, &field)).value)
            .collect::<Vec<BigInt>>();

        let expansion_factor = 4;
        let number_of_colinearity_checks = 4;
        let fri = Fri::new(
            field_generator,
            primitive_root_of_unity_bi.clone(),
            16,
            expansion_factor,
            number_of_colinearity_checks,
            field.q.clone(),
        );
        // let output = vec![123, 20];
        let mut proof_stream: ProofStream = ProofStream::default();
        // proof_stream.set_index(output.len());
        fri.prove(&y_values, &mut proof_stream).unwrap();
        let mut verify_result = fri.verify(&mut proof_stream);
        assert!(verify_result.is_ok(), "FRI verification must succeed");

        // Verify returned values
        let omega = pfb(primitive_root_of_unity_bi, &field);
        for (i, y) in verify_result.unwrap() {
            assert_eq!(
                pol.evaluate(&omega.mod_pow(i.into())).value,
                y,
                "Returned indices and y values must match"
            );
        }

        // change some values and make sure it fails
        for i in 0..expansion_factor {
            y_values[i] = 0.into();
        }
        proof_stream = ProofStream::default();
        fri.prove(&y_values, &mut proof_stream).unwrap();
        verify_result = fri.verify(&mut proof_stream);
        assert!(!verify_result.is_ok(), "FRI verification must not succeed");
    }
}
