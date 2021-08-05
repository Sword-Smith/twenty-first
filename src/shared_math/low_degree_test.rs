use crate::shared_math::other::{bigint, log_2_ceil};
use crate::shared_math::polynomial::Polynomial;
use crate::shared_math::prime_field_element::{PrimeField, PrimeFieldElement};
use crate::shared_math::prime_field_element_big::{PrimeFieldBig, PrimeFieldElementBig};
use crate::shared_math::prime_field_polynomial::PrimeFieldPolynomial;
use crate::util_types::merkle_tree::{CompressedAuthenticationPath, MerkleTree};
use crate::utils::{get_index_from_bytes, get_n_hash_rounds};
use num_bigint::BigInt;
use num_traits::One;
use serde::de::DeserializeOwned;
use serde::Serialize;
use std::convert::TryInto;
use std::error::Error;
use std::fmt;
use std::fmt::{Debug, Display};
use std::result::Result;

#[derive(PartialEq, Eq, Debug)]
pub enum ValidationError {
    BadMerkleProof,
    BadSizedProof,
    NotColinear,
    LastIterationNotConstant,
}

#[derive(Debug)]
struct MyError(String);
impl Error for MyError {}

impl fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Deserialization error for LowDegreeProof: {}", self.0)
    }
}

impl Error for ValidationError {}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Deserialization error for LowDegreeProof: {:?}", self)
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum ProveError {
    BadMaxDegreeValue,
}

impl Error for ProveError {}

impl fmt::Display for ProveError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Deserialization error for LowDegreeProof: {:?}", self)
    }
}

#[cfg_attr(
    feature = "serialization-serde",
    derive(Serialize, Deserialize, Serializer)
)]
#[derive(PartialEq, Debug, Serialize, Clone)]
pub struct LowDegreeProof<T>
where
    // DeserializeOwned is used here to indicate that no data is borrowed
    // in the deserialization process.
    T: Clone + Debug + PartialEq + Serialize,
{
    pub ab_proofs: Vec<Vec<CompressedAuthenticationPath<T>>>,
    challenge_hash_preimages: Vec<Vec<u8>>,
    codeword_size: u32,
    c_proofs: Vec<Vec<CompressedAuthenticationPath<T>>>,
    index_picker_preimage: Vec<u8>,
    max_degree: u32,
    pub merkle_roots: Vec<[u8; 32]>,
    primitive_root_of_unity: T,
    rounds_count: u8,
    pub s: u32,
}

impl<U: Clone + Debug + Display + DeserializeOwned + PartialEq + Serialize> LowDegreeProof<U> {
    pub fn get_abc_indices(&self, round: u8) -> Vec<(usize, usize, usize)> {
        let mut hash_preimage: Vec<u8> = self.index_picker_preimage.clone();
        hash_preimage.push(round);
        let hashes: Vec<[u8; 32]> = get_n_hash_rounds(hash_preimage.as_slice(), self.s);
        let mut abc_indices: Vec<(usize, usize, usize)> =
            Vec::<(usize, usize, usize)>::with_capacity(self.s as usize);
        let half_code_word_size = self.codeword_size as usize >> (round + 1);
        for hash in hashes.iter() {
            let index = get_index_from_bytes(&hash[0..16], half_code_word_size);
            abc_indices.push((index, index + half_code_word_size, index));
        }

        abc_indices
    }
}

impl<U: Clone + Debug + Display + DeserializeOwned + PartialEq + Serialize> LowDegreeProof<U> {
    pub fn from_serialization(
        serialization: Vec<u8>,
        start_index: usize,
    ) -> Result<(LowDegreeProof<U>, usize), Box<dyn Error>> {
        let mut index = start_index;
        // let slice = serialization.clone().as_slice();
        let codeword_size: u32 = bincode::deserialize(&serialization[index..index + 4])?;
        index += 4;
        let max_degree: u32 = bincode::deserialize(&serialization[index..index + 4])?;
        index += 4;
        let s: u32 = bincode::deserialize(&serialization[index..index + 4])?;
        index += 4;
        let size_of_root: u16 = bincode::deserialize(&serialization[index..index + 2])?;
        index += 2;
        let primitive_root_of_unity: U =
            bincode::deserialize(&serialization[index..index + size_of_root as usize])?;
        index += size_of_root as usize;
        let rounds_count = log_2_ceil(max_degree as u64 + 1) as u8;
        let rounds_count_usize = rounds_count as usize;
        let challenge_hash_preimages: Vec<Vec<u8>> = (0..rounds_count_usize)
            .map(|i| serialization[0..((i + 1) * 32 + index)].to_vec())
            .collect();
        let index_picker_preimage =
            serialization[0..((rounds_count_usize + 1) * 32 + index)].to_vec();
        let mut merkle_roots: Vec<[u8; 32]> = Vec::with_capacity(rounds_count_usize + 1);
        for _ in 0usize..(rounds_count_usize + 1) {
            let root: [u8; 32] = serialization[index..index + 32].try_into()?;
            index += 32;
            merkle_roots.push(root);
        }

        let mut c_proofs: Vec<Vec<CompressedAuthenticationPath<U>>> =
            Vec::with_capacity(rounds_count_usize);
        let mut ab_proofs: Vec<Vec<CompressedAuthenticationPath<U>>> =
            Vec::with_capacity(rounds_count_usize);
        for _ in 0..rounds_count {
            let mut proof_size: u16 = bincode::deserialize(&serialization[index..index + 2])?;
            index += 2;
            let c_proof: Vec<CompressedAuthenticationPath<U>> =
                bincode::deserialize_from(&serialization[index..index + proof_size as usize])?;
            index += proof_size as usize;
            c_proofs.push(c_proof);
            proof_size = bincode::deserialize(&serialization[index..index + 2])?;
            index += 2;
            let ab_proof: Vec<CompressedAuthenticationPath<U>> =
                bincode::deserialize_from(&serialization[index..index + proof_size as usize])?;
            index += proof_size as usize;
            ab_proofs.push(ab_proof);
        }
        Ok((
            LowDegreeProof::<U> {
                ab_proofs,
                challenge_hash_preimages,
                codeword_size,
                c_proofs,
                index_picker_preimage,
                max_degree,
                merkle_roots,
                primitive_root_of_unity,
                rounds_count,
                s,
            },
            index,
        ))
    }
}

// Thor wanted to program this for `PrimeFieldElementBig` instead of `BigInt` but
// was unable to, since he could not deserialize a struct with a pointer, like
// PrimeFieldElementBig has. So the solution is to provide the modulus, as a `BigInt`
// as an input to this function.
pub fn verify_bigint(
    proof: LowDegreeProof<BigInt>,
    modulus: BigInt,
) -> Result<(), ValidationError> {
    let rounds_count: usize = log_2_ceil(proof.max_degree as u64 + 1) as usize;
    if rounds_count != proof.ab_proofs.len()
        || rounds_count != proof.c_proofs.len()
        || rounds_count != proof.challenge_hash_preimages.len()
        || rounds_count + 1 != proof.merkle_roots.len()
    {
        return Err(ValidationError::BadSizedProof);
    }

    let challenge_hashes: Vec<[u8; 32]> = proof
        .challenge_hash_preimages
        .iter()
        .map(|bs| *blake3::hash(bs.as_slice()).as_bytes())
        .collect();
    let challenges: Vec<BigInt> = challenge_hashes
        .iter()
        .map(|x| PrimeFieldElementBig::from_bytes_raw(&modulus, &x[0..16]))
        .collect();
    let mut primitive_root_of_unity = proof.primitive_root_of_unity.clone();

    let field = PrimeFieldBig::new(modulus.clone());
    let mut c_values: Vec<BigInt> = vec![];
    for (i, challenge_bigint) in challenges.iter().enumerate() {
        let abc_indices = proof.get_abc_indices(i as u8);
        let c_indices = abc_indices.iter().map(|x| x.2).collect::<Vec<usize>>();
        let mut ab_indices = Vec::<usize>::with_capacity(2 * abc_indices.len());
        for (a, b, _) in abc_indices.iter() {
            ab_indices.push(*a);
            ab_indices.push(*b);
        }

        c_values = proof.c_proofs[i]
            .iter()
            .map(|x| x.0[0].clone().unwrap().value.unwrap())
            .collect::<Vec<BigInt>>();

        let valid_cs = MerkleTree::verify_multi_proof(
            proof.merkle_roots[i + 1],
            &c_indices,
            &proof.c_proofs[i],
        );
        let valid_abs =
            MerkleTree::verify_multi_proof(proof.merkle_roots[i], &ab_indices, &proof.ab_proofs[i]);
        if !valid_cs || !valid_abs {
            println!(
                "Found invalidity of indices on iteration {}: y = {}, s = {}",
                i, valid_cs, valid_abs
            );
            print!("Invalid proofs:");
            if !valid_abs {
                println!("{:?}", &proof.c_proofs[i]);
            }
            if !valid_cs {
                println!("{:?}", &proof.ab_proofs[i]);
            }
            return Err(ValidationError::BadMerkleProof);
        }

        let root = PrimeFieldElementBig::new(primitive_root_of_unity.clone(), &field);
        for j in 0..proof.s as usize {
            let a_index = ab_indices[2 * j] as i128;
            let a_x_bigint = root.mod_pow_raw(bigint(a_index));
            let a_y_bigint: BigInt = proof.ab_proofs[i][2 * j].get_value();
            let b_index = ab_indices[2 * j + 1] as i128;
            let b_x_bigint = root.mod_pow_raw(bigint(b_index));
            let b_y_bigint: BigInt = proof.ab_proofs[i][2 * j + 1].get_value();
            let c_y_bigint = proof.c_proofs[i][j].get_value();
            let a_x = PrimeFieldElementBig::new(a_x_bigint.clone(), &field);
            let a_y = PrimeFieldElementBig::new(a_y_bigint, &field);
            let b_x = PrimeFieldElementBig::new(b_x_bigint, &field);
            let b_y = PrimeFieldElementBig::new(b_y_bigint, &field);
            let challenge = PrimeFieldElementBig::new(challenge_bigint.to_owned(), &field);
            let c_y = PrimeFieldElementBig::new(c_y_bigint, &field);
            if !Polynomial::are_colinear(&[(a_x, a_y), (b_x, b_y), (challenge, c_y)]) {
                // println!(
                //     "{{({},{}),({},{}),({},{})}} are not colinear",
                //     a_x, a_y, b_x, b_y, challenge, c_y
                // );
                println!("Failed to verify colinearity!");
                return Err(ValidationError::NotColinear);
            } else {
                // println!(
                //     "({}, {}), ({}, {}), ({}, {}) are colinear",
                //     a_x, a_y, b_x, b_y, challenge, c_y
                // );
            }
        }

        primitive_root_of_unity =
            primitive_root_of_unity.clone() * primitive_root_of_unity.clone() % modulus.clone();
    }

    // Base case: Verify that the last merkle tree is a constant function
    // Verify only the c indicies
    if c_values.is_empty() || !c_values.iter().all(|x| c_values[0] == *x) {
        // println!("Last y values were not constant. Got: {:?}", c_values);
        println!("Last y values were not constant.");
        return Err(ValidationError::LastIterationNotConstant);
    }

    Ok(())
}

pub fn verify_i128(proof: LowDegreeProof<i128>, modulus: i128) -> Result<(), ValidationError> {
    let rounds_count: usize = log_2_ceil(proof.max_degree as u64 + 1) as usize;
    if rounds_count != proof.ab_proofs.len()
        || rounds_count != proof.c_proofs.len()
        || rounds_count != proof.challenge_hash_preimages.len()
        || rounds_count + 1 != proof.merkle_roots.len()
    {
        return Err(ValidationError::BadSizedProof);
    }

    let challenge_hashes: Vec<[u8; 32]> = proof
        .challenge_hash_preimages
        .iter()
        .map(|bs| *blake3::hash(bs.as_slice()).as_bytes())
        .collect();
    let challenges: Vec<i128> = challenge_hashes
        .iter()
        .map(|x| PrimeFieldElement::from_bytes_raw(&modulus, &x[0..16]))
        .collect();
    let mut number_of_leaves = proof.codeword_size as usize;
    let mut primitive_root_of_unity = proof.primitive_root_of_unity;

    let field = PrimeField::new(modulus);
    let mut c_values: Vec<i128> = vec![];
    for (i, challenge) in challenges.iter().enumerate() {
        let mut hash_preimage: Vec<u8> = proof.index_picker_preimage.clone();
        hash_preimage.push(i as u8);
        let hashes = get_n_hash_rounds(hash_preimage.as_slice(), proof.s);
        let mut c_indices: Vec<usize> = vec![];
        let mut ab_indices: Vec<usize> = vec![];
        for hash in hashes.iter() {
            let c_index = get_index_from_bytes(&hash[0..16], number_of_leaves / 2);
            c_indices.push(c_index);
            let a_index = c_index;
            ab_indices.push(a_index);
            let b_index = c_index + number_of_leaves / 2;
            ab_indices.push(b_index);
        }
        number_of_leaves /= 2;
        c_values = proof.c_proofs[i]
            .iter()
            .map(|x| x.0[0].as_ref().unwrap().value.unwrap())
            .collect::<Vec<i128>>();

        let valid_cs = MerkleTree::verify_multi_proof(
            proof.merkle_roots[i + 1],
            &c_indices,
            &proof.c_proofs[i],
        );
        let valid_abs =
            MerkleTree::verify_multi_proof(proof.merkle_roots[i], &ab_indices, &proof.ab_proofs[i]);
        if !valid_cs || !valid_abs {
            println!(
                "Found invalidity of indices on iteration {}: y = {}, s = {}",
                i, valid_cs, valid_abs
            );
            print!("Invalid proofs:");
            if !valid_abs {
                println!("{:?}", &proof.c_proofs[i]);
            }
            if !valid_cs {
                println!("{:?}", &proof.ab_proofs[i]);
            }
            return Err(ValidationError::BadMerkleProof);
        }

        let root = PrimeFieldElement::new(primitive_root_of_unity, &field);
        for j in 0..proof.s as usize {
            let a_index = ab_indices[2 * j] as i128;
            let a_x = root.mod_pow_raw(a_index);
            let a_y: i128 = proof.ab_proofs[i][2 * j].get_value();
            let b_index = ab_indices[2 * j + 1] as i128;
            let b_x = root.mod_pow_raw(b_index);
            let b_y: i128 = proof.ab_proofs[i][2 * j + 1].get_value();
            let c_y: i128 = proof.c_proofs[i][j].get_value();
            if !PrimeFieldPolynomial::are_colinear_raw(
                &[(a_x, a_y), (b_x, b_y), (*challenge, c_y)],
                modulus,
            ) {
                println!(
                    "{{({},{}),({},{}),({},{})}} are not colinear",
                    a_x, a_y, b_x, b_y, challenge, c_y
                );
                println!("Failed to verify colinearity!");
                return Err(ValidationError::NotColinear);
            } else {
                // println!(
                //     "({}, {}), ({}, {}), ({}, {}) are colinear",
                //     a_x, a_y, b_x, b_y, challenge, c_y
                // );
            }
        }

        primitive_root_of_unity = primitive_root_of_unity * primitive_root_of_unity % modulus;
    }

    // Base case: Verify that the last merkle tree is a constant function
    // Verify only the c indicies
    if c_values.is_empty() || !c_values.iter().all(|&x| c_values[0] == x) {
        println!("Last y values were not constant. Got: {:?}", c_values);
        return Err(ValidationError::LastIterationNotConstant);
    }

    Ok(())
}

fn fri_prover_iteration_bigint(
    codeword: &[BigInt],
    challenge: &BigInt,
    modulus: &BigInt,
    inv_two: &BigInt,
    primitive_root_of_unity: &BigInt,
) -> Vec<BigInt> {
    let mut new_codeword: Vec<BigInt> = vec![bigint(0i128); codeword.len() / 2];

    let mut x: BigInt = BigInt::one();
    for i in 0..new_codeword.len() {
        let (_, x_inv, _) = PrimeFieldElementBig::eea(x.clone(), modulus.to_owned());
        // If codeword is the evaluation of a polynomial of degree N,
        // this is an evaluation of a polynomial of degree N/2
        new_codeword[i] = (((1 + challenge * x_inv.clone()) * codeword[i].clone()
            + (1 - challenge * x_inv.clone()) * codeword[i + codeword.len() / 2].clone())
            * inv_two.to_owned()
            % modulus.to_owned()
            + modulus.to_owned())
            % modulus.to_owned();
        x = x.clone() * primitive_root_of_unity.to_owned() % modulus.to_owned();
    }
    new_codeword
}

fn fri_prover_iteration_i128(
    codeword: &[i128],
    challenge: &i128,
    modulus: &i128,
    inv_two: &i128,
    primitive_root_of_unity: &i128,
) -> Vec<i128> {
    let mut new_codeword: Vec<i128> = vec![0i128; codeword.len() / 2];

    let mut x = 1i128;
    for i in 0..new_codeword.len() {
        let (_, x_inv, _) = PrimeFieldElement::eea(x, *modulus);
        // If codeword is the evaluation of a polynomial of degree N,
        // this is an evaluation of a polynomial of degree N/2
        new_codeword[i] = (((1 + challenge * x_inv) * codeword[i]
            + (1 - challenge * x_inv) * codeword[i + codeword.len() / 2])
            * *inv_two
            % *modulus
            + *modulus)
            % *modulus;
        x = x * *primitive_root_of_unity % modulus;
    }
    new_codeword
}

fn prover_shared<T: Clone + Debug + Serialize + PartialEq>(
    max_degree: u32,
    output: &mut Vec<u8>,
    codeword: &[T],
    s: usize,
    primitive_root_of_unity: T,
) -> Result<(usize, Vec<MerkleTree<T>>), ProveError> {
    let max_degree_plus_one: u32 = max_degree + 1;
    if max_degree_plus_one & (max_degree_plus_one - 1) != 0 {
        return Err(ProveError::BadMaxDegreeValue);
        // panic!("Low-degree prover called for non-power of 2")
    }

    output.append(&mut bincode::serialize(&(codeword.len() as u32)).unwrap());
    output.append(&mut bincode::serialize(&(max_degree as u32)).unwrap());
    output.append(&mut bincode::serialize(&(s as u32)).unwrap());

    // First append length of primitive root, then actual value
    let root_serialization: Vec<u8> = bincode::serialize(&(primitive_root_of_unity)).unwrap();
    let root_serialization_length: u16 = root_serialization.len() as u16;
    output.append(&mut bincode::serialize(&root_serialization_length).unwrap());
    output.append(&mut bincode::serialize(&(primitive_root_of_unity)).unwrap());

    let mt: MerkleTree<T> = MerkleTree::from_vec(codeword);
    let mts: Vec<MerkleTree<T>> = vec![mt];

    output.append(&mut mts[0].get_root().to_vec());
    Ok((log_2_ceil(max_degree_plus_one as u64) as usize, mts))
}

pub fn prover_bigint(
    codeword: &[BigInt],
    modulus: BigInt,
    max_degree: u32,
    s: usize,
    output: &mut Vec<u8>,
    primitive_root_of_unity: BigInt,
) -> Result<LowDegreeProof<BigInt>, ProveError> {
    let (rounds_count, mut mts): (usize, Vec<MerkleTree<BigInt>>) = prover_shared(
        max_degree,
        output,
        codeword,
        s,
        primitive_root_of_unity.clone(),
    )?;
    let mut mut_codeword: Vec<BigInt> = codeword.to_vec();

    // Arrays for return values
    let mut c_proofs: Vec<Vec<CompressedAuthenticationPath<BigInt>>> = vec![];
    let mut ab_proofs: Vec<Vec<CompressedAuthenticationPath<BigInt>>> = vec![];

    // commit phase
    let (_, _, inv2_temp) = PrimeFieldElementBig::eea(modulus.clone(), bigint(2));
    let inv2 = (inv2_temp + modulus.clone()) % modulus.clone();
    let mut primitive_root_of_unity_temp = primitive_root_of_unity.clone();
    let mut challenge_hash_preimages: Vec<Vec<u8>> = vec![];
    for _ in 0..rounds_count {
        // get challenge
        challenge_hash_preimages.push(output.clone());
        let hash = *blake3::hash(output.as_slice()).as_bytes();
        let challenge: BigInt = PrimeFieldElementBig::from_bytes_raw(&modulus, &hash[0..16]);

        // run fri iteration reducing the degree of the polynomial by one half.
        // This is achieved by realizing that
        // P(x) + P(-x) = 2*P_e(x^2) and P(x) - P(-x) = 2*P_o(x^2) where P_e, P_o both
        // have half the degree of P.
        mut_codeword = fri_prover_iteration_bigint(
            &mut_codeword.clone(),
            &challenge,
            &modulus,
            &inv2,
            &primitive_root_of_unity_temp,
        );

        // Construct Merkle Tree from the new codeword of degree `max_degree / 2`
        let mt = MerkleTree::from_vec(&mut_codeword);

        // append root to proof
        output.append(&mut mt.get_root().to_vec());

        // collect into memory
        mts.push(mt);

        // num_rounds += 1;
        primitive_root_of_unity_temp = primitive_root_of_unity_temp.clone()
            * primitive_root_of_unity_temp.clone()
            % modulus.clone();
    }

    // query phase
    // for all subsequent pairs of merkle trees:
    // - do s times:
    // -- sample random point y in L2
    // -- compute square roots s1 s2
    // -- query P1 in y -> beta
    // -- query P2 in s1 -> alpha1
    // -- query P2 in s2 -> alpha2
    // -- check collinearity (s0, alpha0), (s1, alpha1), (y, beta) <-- we don't care about thi right nw>
    let index_picker_preimage = output.clone();
    primitive_root_of_unity_temp = primitive_root_of_unity.clone();
    for i in 0usize..rounds_count {
        let number_of_leaves = mts[i].get_number_of_leafs();
        let mut c_indices: Vec<usize> = vec![];
        let mut ab_indices: Vec<usize> = vec![];

        // it's unrealistic that the number of rounds exceed 256 but this should wrap around if it does
        let mut hash_preimage: Vec<u8> = index_picker_preimage.clone();
        hash_preimage.push(i as u8);

        let hashes = get_n_hash_rounds(hash_preimage.as_slice(), s as u32);
        for hash in hashes.iter() {
            let c_index = get_index_from_bytes(&hash[0..16], number_of_leaves / 2);
            c_indices.push(c_index);
            let s0_index = c_index;
            ab_indices.push(s0_index);
            let s1_index = c_index + number_of_leaves / 2;
            ab_indices.push(s1_index);
        }

        let authentication_paths_c: Vec<CompressedAuthenticationPath<BigInt>> =
            mts[i + 1].get_multi_proof(&c_indices);
        let authentication_paths_ab: Vec<CompressedAuthenticationPath<BigInt>> =
            mts[i].get_multi_proof(&ab_indices);

        // serialize proofs and store in output
        let mut c_paths_encoded = bincode::serialize(&authentication_paths_c.clone()).unwrap();
        output.append(&mut bincode::serialize(&(c_paths_encoded.len() as u16)).unwrap());
        output.append(&mut c_paths_encoded);

        let mut ab_paths_encoded = bincode::serialize(&authentication_paths_ab.clone()).unwrap();
        output.append(&mut bincode::serialize(&(ab_paths_encoded.len() as u16)).unwrap());
        output.append(&mut ab_paths_encoded);

        primitive_root_of_unity_temp = primitive_root_of_unity_temp.clone()
            * primitive_root_of_unity_temp.clone()
            % modulus.clone();

        // Accumulate values to be returned
        c_proofs.push(authentication_paths_c);
        ab_proofs.push(authentication_paths_ab);
    }

    Ok(LowDegreeProof::<BigInt> {
        rounds_count: rounds_count as u8,
        challenge_hash_preimages,
        c_proofs,
        ab_proofs,
        index_picker_preimage,
        s: s as u32,
        merkle_roots: mts.iter().map(|x| x.get_root()).collect::<Vec<[u8; 32]>>(),
        codeword_size: codeword.len() as u32,
        primitive_root_of_unity,
        max_degree,
    })
}

// TODO: We want this implemented for prime field elements, and preferably for
// any finite field/extension field.
// Prove that codeword elements come from the evaluation of a polynomial of
// `degree < codeword.len() / expansion_factor`
pub fn prover_i128(
    codeword: &[i128],
    modulus: i128,
    max_degree: u32,
    s: usize,
    output: &mut Vec<u8>,
    primitive_root_of_unity: i128,
) -> Result<LowDegreeProof<i128>, ProveError> {
    let (rounds_count, mut mts): (usize, Vec<MerkleTree<i128>>) =
        prover_shared(max_degree, output, codeword, s, primitive_root_of_unity)?;

    // Arrays for return values
    let mut c_proofs: Vec<Vec<CompressedAuthenticationPath<i128>>> = vec![];
    let mut ab_proofs: Vec<Vec<CompressedAuthenticationPath<i128>>> = vec![];

    let mut mut_codeword: Vec<i128> = codeword.to_vec();

    // commit phase
    let (_, _, inv2_temp) = PrimeFieldElement::eea(modulus, 2);
    let inv2 = (inv2_temp + modulus) % modulus;
    let mut primitive_root_of_unity_temp = primitive_root_of_unity;
    let mut challenge_hash_preimages: Vec<Vec<u8>> = vec![];
    for _ in 0..rounds_count {
        // get challenge
        challenge_hash_preimages.push(output.clone());
        let hash = *blake3::hash(output.as_slice()).as_bytes();
        let challenge: i128 = PrimeFieldElement::from_bytes_raw(&modulus, &hash[0..16]);

        // run fri iteration reducing the degree of the polynomial by one half.
        // This is achieved by realizing that
        // P(x) + P(-x) = 2*P_e(x^2) and P(x) - P(-x) = 2*P_o(x^2) where P_e, P_o both
        // have half the degree of P.
        mut_codeword = fri_prover_iteration_i128(
            &mut_codeword.clone(),
            &challenge,
            &modulus,
            &inv2,
            &primitive_root_of_unity_temp,
        );

        // Construct Merkle Tree from the new codeword of degree `max_degree / 2`
        let mt = MerkleTree::from_vec(&mut_codeword);

        // append root to proof
        output.append(&mut mt.get_root().to_vec());

        // collect into memory
        mts.push(mt);

        // num_rounds += 1;
        primitive_root_of_unity_temp =
            primitive_root_of_unity_temp * primitive_root_of_unity_temp % modulus;
    }

    // query phase
    // for all subsequent pairs of merkle trees:
    // - do s times:
    // -- sample random point y in L2
    // -- compute square roots s1 s2
    // -- query P1 in y -> beta
    // -- query P2 in s1 -> alpha1
    // -- query P2 in s2 -> alpha2
    // -- check collinearity (s0, alpha0), (s1, alpha1), (y, beta) <-- we don't care about thi right nw>
    // let index_picker_preimage =
    // serialization[0..((rounds_count_usize + 1) * 32 + index)].to_vec();
    let index_picker_preimage = output.clone();
    primitive_root_of_unity_temp = primitive_root_of_unity;
    for i in 0usize..rounds_count {
        let number_of_leaves = mts[i].get_number_of_leafs();
        let mut c_indices: Vec<usize> = vec![];
        let mut ab_indices: Vec<usize> = vec![];

        // it's unrealistic that the number of rounds exceed 256 but this should wrap around if it does
        let mut hash_preimage: Vec<u8> = index_picker_preimage.clone();
        hash_preimage.push(i as u8);

        let hashes = get_n_hash_rounds(hash_preimage.as_slice(), s as u32);
        for hash in hashes.iter() {
            let c_index = get_index_from_bytes(&hash[0..16], number_of_leaves / 2);
            c_indices.push(c_index);
            let s0_index = c_index;
            ab_indices.push(s0_index);
            let s1_index = c_index + number_of_leaves / 2;
            ab_indices.push(s1_index);
        }

        let authentication_paths_c: Vec<CompressedAuthenticationPath<i128>> =
            mts[i + 1].get_multi_proof(&c_indices);
        let authentication_paths_ab: Vec<CompressedAuthenticationPath<i128>> =
            mts[i].get_multi_proof(&ab_indices);

        // serialize proofs and store in output
        let mut c_paths_encoded = bincode::serialize(&authentication_paths_c.clone()).unwrap();
        output.append(&mut bincode::serialize(&(c_paths_encoded.len() as u16)).unwrap());
        output.append(&mut c_paths_encoded);

        let mut ab_paths_encoded = bincode::serialize(&authentication_paths_ab.clone()).unwrap();
        output.append(&mut bincode::serialize(&(ab_paths_encoded.len() as u16)).unwrap());
        output.append(&mut ab_paths_encoded);

        primitive_root_of_unity_temp =
            primitive_root_of_unity_temp * primitive_root_of_unity_temp % modulus;

        // Accumulate values to be returned
        c_proofs.push(authentication_paths_c);
        ab_proofs.push(authentication_paths_ab);
    }

    Ok(LowDegreeProof::<i128> {
        rounds_count: rounds_count as u8,
        challenge_hash_preimages,
        c_proofs,
        ab_proofs,
        index_picker_preimage,
        s: s as u32,
        merkle_roots: mts.iter().map(|x| x.get_root()).collect::<Vec<[u8; 32]>>(),
        codeword_size: codeword.len() as u32,
        primitive_root_of_unity,
        max_degree,
    })
}

#[cfg(test)]
mod test_low_degree_proof {
    use super::*;
    use crate::fft::fast_polynomial_evaluate;
    use crate::shared_math::ntt::ntt;
    use crate::shared_math::prime_field_element::PrimeField;
    use crate::utils::generate_random_numbers;
    use num_traits::Zero;

    #[test]
    fn generate_proof_small_bigint() {
        let mut ret: Option<(PrimeFieldBig, BigInt)> = None;
        PrimeFieldBig::get_field_with_primitive_root_of_unity(4, 100, &mut ret);
        assert_eq!(bigint(101i128), ret.clone().unwrap().0.q);
        let (field, primitive_root_of_unity) = ret.clone().unwrap();
        let power_series = field.get_power_series(primitive_root_of_unity.clone());
        assert_eq!(4, power_series.len());
        assert_eq!(
            vec![bigint(1i128), bigint(10), bigint(100), bigint(91)],
            power_series
        );
        let mut output = vec![];

        // corresponds to the polynomial P(x) = x
        let y_values = power_series;
        let max_degree = 1;
        let s = 5; // The security factor
        let mut proof: LowDegreeProof<BigInt> = prover_bigint(
            &y_values,
            field.q.clone(),
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity.clone(),
        )
        .unwrap();
        assert_eq!(1, proof.max_degree);
        assert_eq!(4, proof.codeword_size);
        assert_eq!(bigint(10), proof.primitive_root_of_unity);
        assert_eq!(1, proof.rounds_count);
        assert_eq!(5, proof.s);
        assert_eq!(1, proof.ab_proofs.len());
        assert_eq!(1, proof.c_proofs.len());
        assert_eq!(2, proof.merkle_roots.len());

        // Verify that abc indices return a value matching that in the authentication paths
        let indicies_round_0 = proof.get_abc_indices(0);
        let selected_ab_values: Vec<(BigInt, BigInt)> = indicies_round_0
            .iter()
            .map(|i| (y_values[i.0].clone(), y_values[i.1].clone()))
            .collect::<Vec<(BigInt, BigInt)>>();
        #[allow(clippy::needless_range_loop)]
        for i in 0..(proof.ab_proofs[0].len() / 2) {
            assert_eq!(
                selected_ab_values[i].0,
                proof.ab_proofs[0][2 * i].get_value()
            );
            assert_eq!(
                selected_ab_values[i].1,
                proof.ab_proofs[0][2 * i + 1].get_value()
            );
        }

        let (mut deserialized_proof, _): (LowDegreeProof<BigInt>, usize) =
            LowDegreeProof::<BigInt>::from_serialization(output.clone(), 0).unwrap();
        assert_eq!(1, deserialized_proof.max_degree);
        assert_eq!(4, deserialized_proof.codeword_size);
        assert_eq!(bigint(10), deserialized_proof.primitive_root_of_unity);
        assert_eq!(1, deserialized_proof.rounds_count);
        assert_eq!(5, deserialized_proof.s);
        assert_eq!(1, deserialized_proof.ab_proofs.len());
        assert_eq!(1, deserialized_proof.c_proofs.len());
        assert_eq!(2, deserialized_proof.merkle_roots.len());
        assert_eq!(proof.ab_proofs, deserialized_proof.ab_proofs);
        assert_eq!(proof.c_proofs, deserialized_proof.c_proofs);
        assert_eq!(
            proof.index_picker_preimage,
            deserialized_proof.index_picker_preimage
        );
        assert_eq!(Ok(()), verify_bigint(proof, field.q.clone()));

        // Change one of the values in a leaf in the committed Merkle tree, and verify that the Merkle proof fails
        output = vec![];
        proof = prover_bigint(
            &y_values,
            field.q.clone(),
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity.clone(),
        )
        .unwrap();
        let mut new_value = proof.ab_proofs[0][1].0[0].clone().unwrap();
        new_value.value = Some(bigint(237));
        proof.ab_proofs[0][1].0[0] = Some(new_value);
        assert_eq!(
            Err(ValidationError::BadMerkleProof),
            verify_bigint(proof, field.q.clone())
        );

        // Verify that the proof still works if the output vector is non-empty at the start
        //  of the proof building
        output = vec![145, 96];
        proof = prover_bigint(
            &y_values,
            field.q.clone(),
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity.clone(),
        )
        .unwrap();
        deserialized_proof = LowDegreeProof::<BigInt>::from_serialization(output.clone(), 2)
            .unwrap()
            .0;
        assert_eq!(deserialized_proof, proof);
        assert_eq!(Ok(()), verify_bigint(deserialized_proof, field.q.clone()));
        assert_eq!(Ok(()), verify_bigint(proof, field.q));
    }

    #[test]
    fn generate_proof_small_i128() {
        let mut ret: Option<(PrimeField, i128)> = None;
        PrimeField::get_field_with_primitive_root_of_unity(4, 100, &mut ret);
        assert_eq!(101i128, ret.clone().unwrap().0.q);
        let (field, primitive_root_of_unity) = ret.clone().unwrap();
        let power_series = field.get_power_series(primitive_root_of_unity);
        assert_eq!(4, power_series.len());
        assert_eq!(vec![1i128, 10, 100, 91], power_series);
        let mut output = vec![];

        // corresponds to the polynomial P(x) = x
        let y_values = power_series;
        let max_degree = 1;
        let s = 5; // The security factor
        let mut proof: LowDegreeProof<i128> = prover_i128(
            &y_values,
            field.q,
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity,
        )
        .unwrap();
        assert_eq!(1, proof.max_degree);
        assert_eq!(4, proof.codeword_size);
        assert_eq!(10, proof.primitive_root_of_unity);
        assert_eq!(1, proof.rounds_count);
        assert_eq!(5, proof.s);
        assert_eq!(1, proof.ab_proofs.len());
        assert_eq!(1, proof.c_proofs.len());
        assert_eq!(2, proof.merkle_roots.len());

        let (mut deserialized_proof, _): (LowDegreeProof<i128>, usize) =
            LowDegreeProof::<i128>::from_serialization(output.clone(), 0).unwrap();
        assert_eq!(1, deserialized_proof.max_degree);
        assert_eq!(4, deserialized_proof.codeword_size);
        assert_eq!(10, deserialized_proof.primitive_root_of_unity);
        assert_eq!(1, deserialized_proof.rounds_count);
        assert_eq!(5, deserialized_proof.s);
        assert_eq!(1, deserialized_proof.ab_proofs.len());
        assert_eq!(1, deserialized_proof.c_proofs.len());
        assert_eq!(2, deserialized_proof.merkle_roots.len());
        assert_eq!(proof.ab_proofs, deserialized_proof.ab_proofs);
        assert_eq!(proof.c_proofs, deserialized_proof.c_proofs);
        assert_eq!(
            proof.index_picker_preimage,
            deserialized_proof.index_picker_preimage
        );
        assert_eq!(Ok(()), verify_i128(proof, field.q));

        // Change one of the values in a leaf in the committed Merkle tree, and verify that the Merkle proof fails
        output = vec![];
        proof = prover_i128(
            &y_values,
            field.q,
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity,
        )
        .unwrap();
        let mut new_value = proof.ab_proofs[0][1].0[0].clone().unwrap();
        new_value.value = Some(237);
        proof.ab_proofs[0][1].0[0] = Some(new_value);
        assert_eq!(
            Err(ValidationError::BadMerkleProof),
            verify_i128(proof, field.q)
        );

        // Verify that the proof still works if the output vector is non-empty
        output = vec![145, 96];
        proof = prover_i128(
            &y_values,
            field.q,
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity,
        )
        .unwrap();
        deserialized_proof = LowDegreeProof::<i128>::from_serialization(output.clone(), 2)
            .unwrap()
            .0;
        assert_eq!(deserialized_proof, proof);
        assert_eq!(Ok(()), verify_i128(deserialized_proof, field.q));
        assert_eq!(Ok(()), verify_i128(proof, field.q));
    }

    #[test]
    fn generate_proof_parabola_bigint() {
        let mut ret: Option<(PrimeFieldBig, BigInt)> = None;
        PrimeFieldBig::get_field_with_primitive_root_of_unity(16, 10000, &mut ret);
        let (field, primitive_root_of_unity_bi) = ret.clone().unwrap();
        let domain: Vec<BigInt> = field.get_power_series(primitive_root_of_unity_bi.clone());
        let max_degree = 3;
        let s = 6;
        let mut y_values = domain
            .iter()
            .map(|x| (6 + x.to_owned() * (2 + 5 * x)) % field.q.clone())
            .collect::<Vec<BigInt>>();
        let mut output = vec![123, 20];
        let mut proof: LowDegreeProof<BigInt> = prover_bigint(
            &y_values,
            field.q.clone(),
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity_bi.clone(),
        )
        .unwrap();

        // Verify that produced proof verifies
        assert_eq!(Ok(()), verify_bigint(proof.clone(), field.q.clone()));

        // Verify that deserialization works *and* gives the expected result
        let deserialized_proof_result =
            LowDegreeProof::<BigInt>::from_serialization(output.clone(), 2);
        let (deserialized_proof, _) = match deserialized_proof_result {
            Err(error) => panic!("{}", error),
            Ok(result) => result,
        };

        assert_eq!(proof, deserialized_proof);

        // Change a single y value such that it no longer corresponds to a polynomil
        // a verify that the test fails
        output = vec![];
        let original_y_values = y_values.clone();
        y_values[3] = y_values[3].clone() + BigInt::one();
        y_values[4] = y_values[4].clone() + BigInt::one();
        proof = prover_bigint(
            &y_values,
            field.q.clone(),
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity_bi.clone(),
        )
        .unwrap();
        assert_eq!(
            Err(ValidationError::LastIterationNotConstant),
            verify_bigint(proof.clone(), field.q.clone())
        );

        // make a proof with a too low max_degree parameter and verify that it fails verification
        // with the expected output
        let wrong_max_degree = 1;
        output = vec![];
        proof = prover_bigint(
            &original_y_values,
            field.q.clone(),
            wrong_max_degree,
            s,
            &mut output,
            primitive_root_of_unity_bi.clone(),
        )
        .unwrap();
        assert_eq!(
            Err(ValidationError::LastIterationNotConstant),
            verify_bigint(proof.clone(), field.q.clone())
        );
    }

    #[test]
    fn generate_proof_parabola_i128() {
        let mut ret: Option<(PrimeField, i128)> = None;
        PrimeField::get_field_with_primitive_root_of_unity(16, 100, &mut ret);
        let (field, primitive_root_of_unity) = ret.clone().unwrap();
        let domain = field.get_power_series(primitive_root_of_unity);
        // coefficients: vec![6, 2, 5] => P(x) = 5x^2 + 2x + 6
        let mut y_values = domain
            .iter()
            .map(|&x| ((6 + x * (2 + 5 * x)) % field.q + field.q) % field.q)
            .collect::<Vec<i128>>();

        let max_degree = 3;
        let s = 6;
        let mut output = vec![124, 62, 98, 10, 207];
        let mut proof: LowDegreeProof<i128> = prover_i128(
            &y_values,
            field.q,
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity,
        )
        .unwrap();
        assert_eq!(
            proof,
            LowDegreeProof::<i128>::from_serialization(output.clone(), 5)
                .unwrap()
                .0
        );
        assert_eq!(Ok(()), verify_i128(proof.clone(), field.q));

        // Change a single y value such that it no longer corresponds to a polynomil
        // a verify that the test fails
        output = vec![];
        let original_y_values = y_values.clone();
        y_values[3] = 100;
        y_values[4] = 100;
        proof = prover_i128(
            &y_values,
            field.q,
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity,
        )
        .unwrap();
        assert_eq!(
            Err(ValidationError::LastIterationNotConstant),
            verify_i128(proof.clone(), field.q)
        );

        // make a proof with a too low max_degree parameter and verify that it fails verification
        // with the expected output
        let wrong_max_degree = 1;
        output = vec![];
        proof = prover_i128(
            &original_y_values,
            field.q,
            wrong_max_degree,
            s,
            &mut output,
            primitive_root_of_unity,
        )
        .unwrap();
        assert_eq!(
            Err(ValidationError::LastIterationNotConstant),
            verify_i128(proof.clone(), field.q)
        );
    }

    #[test]
    fn generate_proof_16_alt_i128() {
        let mut ret: Option<(PrimeField, i128)> = None;
        // should return (field = mod 193; root = 64) for (n = 16, min_value = 113)
        PrimeField::get_field_with_primitive_root_of_unity(16, 113, &mut ret);
        assert_eq!(193i128, ret.clone().unwrap().0.q);
        let (field, primitive_root_of_unity) = ret.clone().unwrap();
        let domain = field.get_power_series(primitive_root_of_unity);
        assert_eq!(16, domain.len());
        assert_eq!(
            vec![1, 64, 43, 50, 112, 27, 184, 3, 192, 129, 150, 143, 81, 166, 9, 190],
            domain
        );
        let mut output = vec![];

        // corresponds to the polynomial P(x) = x
        // degree < codeword.len() / expansion_factor
        let max_degree = 1;
        let s = 2;
        let y_values = domain;
        let proof = prover_i128(
            &y_values,
            field.q,
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity,
        )
        .unwrap();
        assert_eq!(
            proof,
            LowDegreeProof::<i128>::from_serialization(output.clone(), 0)
                .unwrap()
                .0
        );
        assert_eq!(Ok(()), verify_i128(proof, field.q));
    }

    #[test]
    fn generate_proof_16_alt_bigint() {
        let mut ret: Option<(PrimeFieldBig, BigInt)> = None;
        // should return (field = mod 193; root = 64) for (n = 16, min_value = 113)
        PrimeFieldBig::get_field_with_primitive_root_of_unity(16, 113, &mut ret);
        assert_eq!(bigint(193i128), ret.clone().unwrap().0.q);
        let (field, primitive_root_of_unity) = ret.clone().unwrap();
        let domain = field.get_power_series(primitive_root_of_unity.clone());
        let expected_domain: Vec<BigInt> = vec![
            1, 64, 43, 50, 112, 27, 184, 3, 192, 129, 150, 143, 81, 166, 9, 190,
        ]
        .iter()
        .map(|x| bigint(*x))
        .collect();
        assert_eq!(16, domain.len());
        assert_eq!(expected_domain, domain);
        let mut output = vec![];

        // corresponds to the polynomial P(x) = x
        // degree < codeword.len() / expansion_factor
        let max_degree = 1;
        let s = 2;
        let y_values = domain;
        let proof = prover_bigint(
            &y_values,
            field.q.clone(),
            max_degree,
            s,
            &mut output,
            primitive_root_of_unity.clone(),
        )
        .unwrap();
        assert_eq!(
            proof,
            LowDegreeProof::<BigInt>::from_serialization(output.clone(), 0)
                .unwrap()
                .0
        );
        assert_eq!(Ok(()), verify_bigint(proof, field.q));
    }

    #[test]
    fn generate_proof_1024_bigint() {
        let mut ret: Option<(PrimeFieldBig, BigInt)> = None;
        let size = 2usize.pow(14);
        let max_degree = 1023;
        let expected_prime_i128 = 65537i128;
        let expected_prime = bigint(65537i128);
        let expected_root = bigint(81i128); // 1024 degree root of 65537
        PrimeFieldBig::get_field_with_primitive_root_of_unity(size as i128, size as i128, &mut ret);
        let (field_temp, primitive_root_of_unity_bi) = ret.clone().unwrap();
        let field: PrimeFieldBig = field_temp.clone();
        assert_eq!(expected_prime, field.q);
        assert_eq!(expected_root, primitive_root_of_unity_bi);
        let mut coefficients: Vec<BigInt> =
            generate_random_numbers(max_degree + 1, expected_prime_i128)
                .iter()
                .map(|x| bigint(*x))
                .collect();
        println!("length of coefficients = {}", coefficients.len());
        coefficients.extend_from_slice(&vec![BigInt::zero(); size - max_degree - 1]);
        let coefficients_pfes: Vec<PrimeFieldElementBig> = coefficients
            .iter()
            .map(|x| PrimeFieldElementBig::new(x.to_owned(), &field))
            .collect();
        println!("length of expanded coefficients = {}", coefficients.len());
        let primitive_root_of_unity: PrimeFieldElementBig =
            PrimeFieldElementBig::new(primitive_root_of_unity_bi.clone(), &field);
        let y_values_pfes = ntt(
            coefficients_pfes.as_slice(),
            &primitive_root_of_unity.clone(),
        );
        println!("length of y_values_pfes = {}", y_values_pfes.len());
        let mut y_values: Vec<BigInt> = y_values_pfes.iter().map(|x| x.to_owned().value).collect();

        let mut output = vec![1, 2];

        let s = 20;
        let mut proof = prover_bigint(
            &y_values,
            field.q.clone(),
            max_degree as u32,
            s,
            &mut output,
            primitive_root_of_unity_bi.clone(),
        )
        .unwrap();
        println!("rounds in proof = {}", proof.rounds_count);
        assert_eq!(
            proof,
            LowDegreeProof::<BigInt>::from_serialization(output.clone(), 2)
                .unwrap()
                .0
        );
        assert_eq!(Ok(()), verify_bigint(proof.clone(), field.q.clone()));

        // Verify that the index picker matches picked indices for ab_proof
        let indices = proof.get_abc_indices(0);
        let selected_ab_values: Vec<(BigInt, BigInt)> = indices
            .iter()
            .map(|i| (y_values[i.0].clone(), y_values[i.1].clone()))
            .collect::<Vec<(BigInt, BigInt)>>();
        #[allow(clippy::needless_range_loop)]
        for j in 0..(proof.ab_proofs[0].len() / 2) {
            assert_eq!(
                selected_ab_values[j].0,
                proof.ab_proofs[0][2 * j].get_value()
            );
            assert_eq!(
                selected_ab_values[j].1,
                proof.ab_proofs[0][2 * j + 1].get_value()
            );
        }

        // Verify that a 1023 degree polynomial cannot be verified as a degree 512 polynomial
        output = vec![1, 2];
        proof = prover_bigint(
            &y_values,
            field.q.clone(),
            511,
            s,
            &mut output,
            primitive_root_of_unity_bi.clone(),
        )
        .unwrap();
        println!("rounds in proof = {}", proof.rounds_count);
        assert_eq!(
            Err(ValidationError::LastIterationNotConstant),
            verify_bigint(proof, field.q.clone())
        );

        // Change a single y value such that it no longer corresponds to a polynomial
        // and verify that the test fails
        output = vec![];
        y_values[3] = y_values[3].clone() + 1;
        proof = prover_bigint(
            &y_values,
            field.q.clone(),
            max_degree as u32,
            s,
            &mut output,
            primitive_root_of_unity_bi,
        )
        .unwrap();
        assert_eq!(
            proof,
            LowDegreeProof::<BigInt>::from_serialization(output.clone(), 0)
                .unwrap()
                .0
        );
        assert_eq!(
            Err(ValidationError::LastIterationNotConstant),
            verify_bigint(proof, field.q.clone())
        );
    }

    #[test]
    fn generate_proof_1024_i128() {
        let mut ret: Option<(PrimeField, i128)> = None;
        let size = 2usize.pow(14);
        let max_degree = 1023;
        PrimeField::get_field_with_primitive_root_of_unity(size as i128, size as i128, &mut ret);
        let (field_temp, primitive_root_of_unity) = ret.clone().unwrap();
        let field: PrimeField = field_temp.clone();
        assert_eq!(65537i128, field.q);
        assert_eq!(81i128, primitive_root_of_unity);
        let mut coefficients = generate_random_numbers(max_degree + 1, field.q);
        println!("length of coefficients = {}", coefficients.len());
        coefficients.extend_from_slice(&vec![0; size - max_degree - 1]);
        println!("length of expanded coefficients = {}", coefficients.len());
        let mut y_values =
            fast_polynomial_evaluate(coefficients.as_slice(), field.q, primitive_root_of_unity);
        println!("length of y_values = {}", y_values.len());

        let mut output = vec![1, 2];

        let s = 80;
        let mut proof = prover_i128(
            &y_values,
            field.q,
            max_degree as u32,
            s,
            &mut output,
            primitive_root_of_unity,
        )
        .unwrap();
        println!("rounds in proof = {}", proof.rounds_count);
        assert_eq!(
            proof,
            LowDegreeProof::<i128>::from_serialization(output.clone(), 2)
                .unwrap()
                .0
        );
        assert_eq!(Ok(()), verify_i128(proof, field.q));

        // Verify that a 1023 degree polynomial cannot be verified as a degree 512 polynomial
        output = vec![1, 2];
        proof = prover_i128(
            &y_values,
            field.q,
            511,
            s,
            &mut output,
            primitive_root_of_unity,
        )
        .unwrap();
        println!("rounds in proof = {}", proof.rounds_count);
        assert_eq!(
            Err(ValidationError::LastIterationNotConstant),
            verify_i128(proof, field.q)
        );

        // Change a single y value such that it no longer corresponds to a polynomial
        // and verify that the test fails
        output = vec![];
        y_values[3] ^= 1;
        proof = prover_i128(
            &y_values,
            field.q,
            max_degree as u32,
            s,
            &mut output,
            primitive_root_of_unity,
        )
        .unwrap();
        assert_eq!(
            proof,
            LowDegreeProof::<i128>::from_serialization(output.clone(), 0)
                .unwrap()
                .0
        );
        assert_eq!(
            Err(ValidationError::LastIterationNotConstant),
            verify_i128(proof, field.q)
        );
    }
}
