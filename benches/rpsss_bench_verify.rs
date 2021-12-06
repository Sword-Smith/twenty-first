use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use num_bigint::BigInt;
use twenty_first::shared_math::{
    prime_field_element_big::{PrimeFieldBig, PrimeFieldElementBig},
    rescue_prime_stark::RescuePrime,
    rpsss::{Signature, RPSSS},
    stark::Stark,
};

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

fn rpsss_bench_verify(c: &mut Criterion) {
    let modulus: BigInt = (407u128 * (1 << 119) + 1).into();
    let field = PrimeFieldBig::new(modulus);
    let (mut stark, rp) = get_tutorial_stark(&field);
    let rpsss = RPSSS {
        field: field.clone(),
        stark: stark.clone(),
        rp,
    };
    let document_string: String = "Hello Neptune!".to_string();
    let document: Vec<u8> = document_string.clone().into_bytes();

    // Calculate the index, AKA preprocessing
    stark.prover_preprocess();

    let (sk, pk) = rpsss.keygen();
    let signature: Signature = rpsss.sign(&sk, &document).unwrap();
    let mut group_verify = c.benchmark_group("rpsss_bench_verify");
    group_verify
        .bench_with_input(
            BenchmarkId::from_parameter("rpsss_bench_verify"),
            &1,
            |b, _| {
                b.iter(|| rpsss.verify(&pk, &signature, &document));
            },
        )
        .sample_size(10);
    group_verify.finish();
}
criterion_group!(benches, rpsss_bench_verify);
criterion_main!(benches);
