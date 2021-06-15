use crate::shared_math::prime_field_element::PrimeFieldElement;
use crate::util_types::merkle_tree_vector::{MerkleTreeVector, Node};
use crate::utils::{get_index_from_bytes, get_n_hash_rounds};

pub fn fri_prover_iteration<'b>(
    codeword: &[i128],
    challenge: &i128,
    modulus: &i128,
    inv_two: &i128,
) -> Vec<i128> {
    // let mut new_codeword: Vec<i128> = Vec::with_capacity(codeword.len() / 2);
    let mut new_codeword: Vec<i128> = vec![0i128; codeword.len() / 2];

    for i in 0..new_codeword.len() {
        // If codeword is the evaluation of a polynomial of degree N,
        // this is an evaluation of a polynomial of degree N/2
        new_codeword[i] = ((challenge + 1) * codeword[i]
            + (challenge - 1) * codeword[i + codeword.len() / 2])
            * *inv_two
            % *modulus;
    }
    new_codeword
}

// TODO: We want this implemented for prime field elements, and preferably for
// any finite field/extension field.
// Prove that codeword elements come from the evaluation of a polynomial of degree
// < codeword.len() / rho
pub fn prover<'a>(codeword: &[i128], modulus: i128, rho: usize, s: usize, output: &mut Vec<u8>) {
    let mut mts: Vec<MerkleTreeVector<i128>> = vec![];
    mts.push(MerkleTreeVector::from_vec(codeword));
    let mut mut_codeword: Vec<i128> = codeword.to_vec().clone();

    // commit phase
    let (_, inv2, _) = PrimeFieldElement::eea(modulus, 2);
    let mut num_rounds = 0;
    while mut_codeword.len() >= rho {
        // get challenge
        println!("Length of mut_codeword: {}", mut_codeword.len());
        let hash = *blake3::hash(output.as_slice()).as_bytes();
        let challenge: i128 = PrimeFieldElement::from_bytes_raw(&modulus, &hash[0..16]);

        // run fri iteration
        mut_codeword = fri_prover_iteration(&mut_codeword.clone(), &challenge, &modulus, &inv2);
        // wrap into merkle tree
        let mt = MerkleTreeVector::from_vec(&mut_codeword);
        // collect into cache
        mts.push(mt.clone());
        // append root to proof
        output.append(&mut mt.get_root().to_vec());
        num_rounds += 1;
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
    // let authentication_paths: Vec<Vec<Option<Node<i128>>>> = vec![];
    for i in 0usize..num_rounds - 1 {
        let n = mts[i].get_number_of_leafs();
        let mut y_indices: Vec<usize> = vec![];
        let mut s_indices: Vec<usize> = vec![];
        // let mut s1_indices: Vec<usize> = vec![];
        // let hash = *blake3::hash(output.as_slice()).as_bytes();
        let hashes = get_n_hash_rounds(output.as_slice(), s);
        for j in 0usize..s {
            let y_index = get_index_from_bytes(&hashes[j][0..16], n / 2);
            y_indices.push(y_index);
            let s0_index = y_index;
            s_indices.push(s0_index);
            let s1_index = y_index + n / 2;
            s_indices.push(s1_index);
        }
        let authentication_paths_y: Vec<Vec<Option<Node<i128>>>> =
            mts[i + i].get_multi_proof(y_indices);
        let authentication_paths_s: Vec<Vec<Option<Node<i128>>>> =
            mts[i].get_multi_proof(s_indices);
        output.append(&mut bincode::serialize(&authentication_paths_y.clone()).unwrap());
        output.append(&mut bincode::serialize(&authentication_paths_s.clone()).unwrap());
    }
}

#[cfg(test)]
mod test_utils {
    use super::*;
    use crate::utils::decode_hex;

    #[test]
    fn generate_proof() {
        let mut output = vec![];
        prover(
            &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
            31,
            4,
            4,
            &mut output,
        );
        println!("{:?}", output);
    }
}
