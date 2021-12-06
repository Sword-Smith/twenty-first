use num_bigint::BigInt;

use crate::shared_math::prime_field_element_big::{PrimeFieldBig, PrimeFieldElementBig};
use crate::shared_math::stark::BoundaryConstraint;
use crate::shared_math::traits::IdentityValues;

use super::mpolynomial::MPolynomial;
use super::polynomial::Polynomial;

#[derive(Debug, Clone)]
pub struct RescuePrime<'a> {
    // field: PrimeFieldBig,
    pub m: usize,
    // rate: usize,
    // capacity: usize,
    pub steps_count: usize,
    alpha: BigInt,
    alpha_inv: BigInt,
    mds: Vec<Vec<PrimeFieldElementBig<'a>>>,
    mds_inv: Vec<Vec<PrimeFieldElementBig<'a>>>,
    round_constants: Vec<PrimeFieldElementBig<'a>>,
}

impl<'a> RescuePrime<'a> {
    pub fn from_tutorial(field: &'a PrimeFieldBig) -> Self {
        let required_field = PrimeFieldBig::new((407u128 * (1 << 119) + 1).into());
        assert!(
            field.q == required_field.q,
            "Field must be p = 407*2^119 + 1"
        );
        // let required_field = PrimeFieldBig::new((407u128 * (1 << 119) + 1).into());
        let mds: Vec<Vec<PrimeFieldElementBig<'a>>> = vec![
            vec![
                PrimeFieldElementBig::new(
                    270497897142230380135924736767050121214u128.into(),
                    field,
                ),
                PrimeFieldElementBig::new(4.into(), field),
            ],
            vec![
                PrimeFieldElementBig::new(
                    270497897142230380135924736767050121205u128.into(),
                    field,
                ),
                PrimeFieldElementBig::new(13.into(), field),
            ],
        ];
        let mds_inv: Vec<Vec<PrimeFieldElementBig<'a>>> = vec![
            vec![
                PrimeFieldElementBig::new(
                    210387253332845851216830350818816760948u128.into(),
                    field,
                ),
                PrimeFieldElementBig::new(60110643809384528919094385948233360270u128.into(), field),
            ],
            vec![
                PrimeFieldElementBig::new(90165965714076793378641578922350040407u128.into(), field),
                PrimeFieldElementBig::new(
                    180331931428153586757283157844700080811u128.into(),
                    field,
                ),
            ],
        ];

        // Each round has two round constants: `fst_rc` and `snd_rc`.
        // `fst_rc` values are indexed in the below array as:
        // `2 * round_number * register_counter + register_index`
        // `snd_rc` values are indexed in the below array as:
        // `2 * round_number * register_counter + register_index`
        let round_constants_u128: Vec<u128> = vec![
            174420698556543096520990950387834928928u128,
            109797589356993153279775383318666383471u128,
            228209559001143551442223248324541026000u128,
            268065703411175077628483247596226793933u128,
            250145786294793103303712876509736552288u128,
            154077925986488943960463842753819802236u128,
            204351119916823989032262966063401835731u128,
            57645879694647124999765652767459586992u128,
            102595110702094480597072290517349480965u128,
            8547439040206095323896524760274454544u128,
            50572190394727023982626065566525285390u128,
            87212354645973284136664042673979287772u128,
            64194686442324278631544434661927384193u128,
            23568247650578792137833165499572533289u128,
            264007385962234849237916966106429729444u128,
            227358300354534643391164539784212796168u128,
            179708233992972292788270914486717436725u128,
            102544935062767739638603684272741145148u128,
            65916940568893052493361867756647855734u128,
            144640159807528060664543800548526463356u128,
            58854991566939066418297427463486407598u128,
            144030533171309201969715569323510469388u128,
            264508722432906572066373216583268225708u128,
            22822825100935314666408731317941213728u128,
            33847779135505989201180138242500409760u128,
            146019284593100673590036640208621384175u128,
            51518045467620803302456472369449375741u128,
            73980612169525564135758195254813968438u128,
            31385101081646507577789564023348734881u128,
            270440021758749482599657914695597186347u128,
            185230877992845332344172234234093900282u128,
            210581925261995303483700331833844461519u128,
            233206235520000865382510460029939548462u128,
            178264060478215643105832556466392228683u128,
            69838834175855952450551936238929375468u128,
            75130152423898813192534713014890860884u128,
            59548275327570508231574439445023390415u128,
            43940979610564284967906719248029560342u128,
            95698099945510403318638730212513975543u128,
            77477281413246683919638580088082585351u128,
            206782304337497407273753387483545866988u128,
            141354674678885463410629926929791411677u128,
            19199940390616847185791261689448703536u128,
            177613618019817222931832611307175416361u128,
            267907751104005095811361156810067173120u128,
            33296937002574626161968730356414562829u128,
            63869971087730263431297345514089710163u128,
            200481282361858638356211874793723910968u128,
            69328322389827264175963301685224506573u128,
            239701591437699235962505536113880102063u128,
            17960711445525398132996203513667829940u128,
            219475635972825920849300179026969104558u128,
            230038611061931950901316413728344422823u128,
            149446814906994196814403811767389273580u128,
            25535582028106779796087284957910475912u128,
            93289417880348777872263904150910422367u128,
            4779480286211196984451238384230810357u128,
            208762241641328369347598009494500117007u128,
            34228805619823025763071411313049761059u128,
            158261639460060679368122984607245246072u128,
            65048656051037025727800046057154042857u128,
            134082885477766198947293095565706395050u128,
            23967684755547703714152865513907888630u128,
            8509910504689758897218307536423349149u128,
            232305018091414643115319608123377855094u128,
            170072389454430682177687789261779760420u128,
            62135161769871915508973643543011377095u128,
            15206455074148527786017895403501783555u128,
            201789266626211748844060539344508876901u128,
            179184798347291033565902633932801007181u128,
            9615415305648972863990712807943643216u128,
            95833504353120759807903032286346974132u128,
            181975981662825791627439958531194157276u128,
            267590267548392311337348990085222348350u128,
            49899900194200760923895805362651210299u128,
            89154519171560176870922732825690870368u128,
            265649728290587561988835145059696796797u128,
            140583850659111280842212115981043548773u128,
            266613908274746297875734026718148328473u128,
            236645120614796645424209995934912005038u128,
            265994065390091692951198742962775551587u128,
            59082836245981276360468435361137847418u128,
            26520064393601763202002257967586372271u128,
            108781692876845940775123575518154991932u128,
            138658034947980464912436420092172339656u128,
            45127926643030464660360100330441456786u128,
            210648707238405606524318597107528368459u128,
            42375307814689058540930810881506327698u128,
            237653383836912953043082350232373669114u128,
            236638771475482562810484106048928039069u128,
            168366677297979943348866069441526047857u128,
            195301262267610361172900534545341678525u128,
            2123819604855435621395010720102555908u128,
            96986567016099155020743003059932893278u128,
            248057324456138589201107100302767574618u128,
            198550227406618432920989444844179399959u128,
            177812676254201468976352471992022853250u128,
            211374136170376198628213577084029234846u128,
            105785712445518775732830634260671010540u128,
            122179368175793934687780753063673096166u128,
            126848216361173160497844444214866193172u128,
            22264167580742653700039698161547403113u128,
            234275908658634858929918842923795514466u128,
            189409811294589697028796856023159619258u128,
            75017033107075630953974011872571911999u128,
            144945344860351075586575129489570116296u128,
            261991152616933455169437121254310265934u128,
            18450316039330448878816627264054416127u128,
        ];
        let round_constants: Vec<PrimeFieldElementBig<'a>> = round_constants_u128
            .into_iter()
            .map(|v| PrimeFieldElementBig::new(v.into(), field))
            .collect();

        Self {
            // field: field.clone(),
            m: 2,
            // rate: 1,
            // capacity: 1,
            steps_count: 27,
            alpha: 3.into(),
            alpha_inv: 180331931428153586757283157844700080811u128.into(),
            mds,
            mds_inv,
            round_constants,
        }
    }

    fn hash_round(
        &self,
        input_state: Vec<PrimeFieldElementBig<'a>>,
        round_number: usize,
    ) -> Vec<PrimeFieldElementBig<'a>> {
        // S-box
        let mut state: Vec<PrimeFieldElementBig<'a>> = input_state
            .iter()
            .map(|v| v.mod_pow(self.alpha.clone()))
            .collect();

        // Matrix
        let mut temp: Vec<PrimeFieldElementBig> = vec![input_state[0].ring_zero(); self.m];
        #[allow(clippy::needless_range_loop)]
        for i in 0..self.m {
            for j in 0..self.m {
                temp[i] = temp[i].clone() + self.mds[i][j].clone() * state[j].clone();
            }
        }

        // Add rounding constants
        state = temp
            .into_iter()
            .enumerate()
            .map(|(i, val)| val + self.round_constants[2 * round_number * self.m + i].clone())
            .collect();

        // Backward half-round
        // S-box
        state = state
            .iter()
            .map(|v| v.mod_pow(self.alpha_inv.clone()))
            .collect();

        // Matrix
        temp = vec![input_state[0].ring_zero(); self.m];
        #[allow(clippy::needless_range_loop)]
        for i in 0..self.m {
            for j in 0..self.m {
                temp[i] = temp[i].clone() + self.mds[i][j].clone() * state[j].clone();
            }
        }

        // Add rounding constants
        state = temp
            .into_iter()
            .enumerate()
            .map(|(i, val)| {
                val + self.round_constants[2 * round_number * self.m + self.m + i].clone()
            })
            .collect();

        state
    }

    /// Return the Rescue-Prime hash value
    pub fn hash(&self, input: &PrimeFieldElementBig<'a>) -> PrimeFieldElementBig<'a> {
        let mut state = vec![input.ring_zero(); self.m];
        state[0] = input.to_owned();

        state = (0..self.steps_count).fold(state, |state, i| self.hash_round(state, i));

        state[0].clone()
    }

    pub fn trace(&self, input: &PrimeFieldElementBig<'a>) -> Vec<Vec<PrimeFieldElementBig>> {
        let mut trace: Vec<Vec<PrimeFieldElementBig>> = vec![];
        let mut state = vec![input.ring_zero(); self.m];
        state[0] = input.to_owned();
        trace.push(state.clone());

        // It could be cool to write this with `scan` instead of a for-loop, but I couldn't get that to work
        for i in 0..self.steps_count {
            let next_state = self.hash_round(state, i);
            trace.push(next_state.clone());
            state = next_state;
        }

        trace
    }

    pub fn eval_and_trace(
        &self,
        input: &PrimeFieldElementBig<'a>,
    ) -> (PrimeFieldElementBig, Vec<Vec<PrimeFieldElementBig>>) {
        let trace = self.trace(input);
        let output = trace.last().unwrap()[0].clone();

        (output, trace)
    }

    /// Return a pair of a list of polynomials, first element in the pair,
    /// (first_round_constants[register], second_round_constants[register])
    pub fn get_round_constant_polynomials(
        &self,
        omicron: &'a PrimeFieldElementBig,
    ) -> (
        Vec<MPolynomial<PrimeFieldElementBig<'a>>>,
        Vec<MPolynomial<PrimeFieldElementBig<'a>>>,
    ) {
        let domain = omicron.get_generator_domain();
        let mut first_round_constants: Vec<MPolynomial<PrimeFieldElementBig>> = vec![];
        for i in 0..self.m {
            let values: Vec<PrimeFieldElementBig> = self
                .round_constants
                .clone()
                .into_iter()
                .skip(i)
                .step_by(2 * self.m)
                .collect();
            // let coefficients = intt(&values, omicron);
            let points: Vec<(PrimeFieldElementBig, PrimeFieldElementBig)> = domain
                .clone()
                .iter()
                .zip(values.iter())
                .map(|(x, y)| (x.to_owned(), y.to_owned()))
                .collect();
            let coefficients = Polynomial::slow_lagrange_interpolation(&points).coefficients;
            first_round_constants.push(MPolynomial::lift(Polynomial { coefficients }, 0));
        }

        let mut second_round_constants: Vec<MPolynomial<PrimeFieldElementBig>> = vec![];
        for i in 0..self.m {
            let values: Vec<PrimeFieldElementBig> = self
                .round_constants
                .clone()
                .into_iter()
                .skip(i + self.m)
                .step_by(2 * self.m)
                .collect();
            // let coefficients = intt(&values, omicron);
            let points: Vec<(PrimeFieldElementBig, PrimeFieldElementBig)> = domain
                .clone()
                .iter()
                .zip(values.iter())
                .map(|(x, y)| (x.to_owned(), y.to_owned()))
                .collect();
            let coefficients = Polynomial::slow_lagrange_interpolation(&points).coefficients;
            second_round_constants.push(MPolynomial::lift(Polynomial { coefficients }, 0));
        }

        (first_round_constants, second_round_constants)
    }

    // Returns the multivariate polynomial which takes the triplet (domain, trace, next_trace) and
    // returns composition polynomial, which is the evaluation of the air for a specific trace.
    // AIR: [F_p x F_p^m x F_p^m] --> F_p^m
    // The composition polynomial values are low-degree polynomial combinations
    // (as opposed to linear combinations) of the values:
    // `domain` (scalar), `trace` (vector), `next_trace` (vector).
    pub fn get_air_constraints(
        &self,
        omicron: &'a PrimeFieldElementBig,
    ) -> Vec<MPolynomial<PrimeFieldElementBig<'a>>> {
        let (first_step_constants, second_step_constants) =
            self.get_round_constant_polynomials(omicron);

        let variables = MPolynomial::variables(1 + 2 * self.m, omicron.ring_one());
        let previous_state = &variables[1..(self.m + 1)];
        let next_state = &variables[(self.m + 1)..(2 * self.m + 1)];
        let one = omicron.ring_one();
        let mut air: Vec<MPolynomial<PrimeFieldElementBig>> = vec![];
        #[allow(clippy::needless_range_loop)]
        for i in 0..self.m {
            let mut lhs = MPolynomial::from_constant(omicron.ring_zero());
            for k in 0..self.m {
                lhs = lhs
                    + previous_state[k]
                        .mod_pow(self.alpha.clone(), one.clone())
                        .scalar_mul(self.mds[i][k].clone());
            }
            lhs = lhs + first_step_constants[i].clone();

            let mut rhs = MPolynomial::from_constant(omicron.ring_zero());
            for k in 0..self.m {
                rhs = rhs
                    + (next_state[k].clone() - second_step_constants[k].clone())
                        .scalar_mul(self.mds_inv[i][k].clone());
            }
            rhs = rhs.mod_pow(self.alpha.clone(), one.clone());

            air.push(lhs - rhs);
        }

        air
    }

    pub fn get_boundary_constraints(
        &self,
        output_element: &'a PrimeFieldElementBig,
    ) -> Vec<BoundaryConstraint> {
        vec![
            BoundaryConstraint {
                cycle: 0,
                register: 1,
                value: output_element.ring_zero(),
            },
            BoundaryConstraint {
                cycle: self.steps_count,
                register: 0,
                value: output_element.to_owned(),
            },
        ]
    }
}

#[cfg(test)]
mod rescue_prime_start_test {
    use crate::{shared_math::stark::Stark, util_types::proof_stream::ProofStream};

    use super::*;

    #[test]
    fn hash_test_vectors() {
        // Values found on:
        // https://github.com/aszepieniec/stark-anatomy/blob/master/code/test_rescue_prime.py
        let field = PrimeFieldBig::new((407u128 * (1 << 119) + 1).into());
        let rescue_prime_stark = RescuePrime::from_tutorial(&field);

        // rescue prime test vector 1
        let one = PrimeFieldElementBig::new(1.into(), &field);
        let expected_output_one =
            PrimeFieldElementBig::new(244180265933090377212304188905974087294u128.into(), &field);
        let calculated_output_of_one = rescue_prime_stark.hash(&one);
        assert_eq!(expected_output_one, calculated_output_of_one);

        // rescue prime test vector 1, with trace
        let calculated_trace_of_one = rescue_prime_stark.trace(&one);
        assert_eq!(
            expected_output_one,
            calculated_trace_of_one.last().unwrap()[0]
        );

        // rescue prime test vector 2
        let input_2 =
            PrimeFieldElementBig::new(57322816861100832358702415967512842988u128.into(), &field);
        let expected_output_2 =
            PrimeFieldElementBig::new(89633745865384635541695204788332415101u128.into(), &field);
        let calculated_output_2 = rescue_prime_stark.hash(&input_2);
        assert_eq!(expected_output_2, calculated_output_2);

        // rescue prime test vector 2, with trace
        let calculated_trace_2 = rescue_prime_stark.trace(&input_2);
        assert_eq!(expected_output_2, calculated_trace_2.last().unwrap()[0]);
        assert_eq!(input_2, calculated_trace_2.first().unwrap()[0]);
        assert_eq!(rescue_prime_stark.steps_count + 1, calculated_trace_2.len());
    }

    #[test]
    fn air_is_zero_on_execution_trace() {
        let field = PrimeFieldBig::new((407u128 * (1 << 119) + 1).into());
        let rescue_prime_stark = RescuePrime::from_tutorial(&field);

        // rescue prime test vector 1
        let omicron_res = field.get_primitive_root_of_unity(1 << 5);
        let omicron = omicron_res.0.unwrap();

        // Verify that the round constants polynomials are correct
        let (fst_rc_pol, snd_rc_pol) = rescue_prime_stark.get_round_constant_polynomials(&omicron);
        for step in 0..rescue_prime_stark.steps_count {
            let point = vec![omicron.mod_pow(step.into())];
            for register in 0..rescue_prime_stark.m {
                let fst_eval = fst_rc_pol[register].evaluate(&point);
                assert_eq!(
                    rescue_prime_stark.round_constants[2 * step * rescue_prime_stark.m + register],
                    fst_eval
                );
            }
            for register in 0..rescue_prime_stark.m {
                let snd_eval = snd_rc_pol[register].evaluate(&point);
                assert_eq!(
                    rescue_prime_stark.round_constants
                        [2 * step * rescue_prime_stark.m + rescue_prime_stark.m + register],
                    snd_eval
                );
            }
        }

        // Counted 108 round constants in Python code, verify that we agree
        assert_eq!(
            108,
            rescue_prime_stark.steps_count * 2 * rescue_prime_stark.m
        );

        // Verify that the AIR constraints evaluation over the trace
        // is zero along the trace
        let input_2 =
            PrimeFieldElementBig::new(57322816861100832358702415967512842988u128.into(), &field);
        let trace = rescue_prime_stark.trace(&input_2);
        let air_constraints = rescue_prime_stark.get_air_constraints(&omicron);

        for step in 0..rescue_prime_stark.steps_count - 1 {
            for air_constraint in air_constraints.iter() {
                let mut point = vec![];
                point.push(omicron.mod_pow(step.into()));
                point.push(trace[step][0].clone());
                point.push(trace[step][1].clone());
                point.push(trace[step + 1][0].clone());
                point.push(trace[step + 1][1].clone());
                let eval = air_constraint.evaluate(&point);
                assert!(eval.is_zero());
            }
        }
    }

    #[test]
    fn rp_stark_test() {
        let field = PrimeFieldBig::new((407u128 * (1 << 119) + 1).into());
        let expansion_factor = 4usize;
        let colinearity_checks_count = 2usize;
        let transition_constraints_degree = 2usize;
        let generator =
            PrimeFieldElementBig::new(85408008396924667383611388730472331217u128.into(), &field);
        let rescue_prime_stark = RescuePrime::from_tutorial(&field);

        let mut stark = Stark::new(
            &field,
            expansion_factor,
            colinearity_checks_count,
            rescue_prime_stark.m,
            rescue_prime_stark.steps_count + 1,
            transition_constraints_degree,
            generator,
        );
        stark.prover_preprocess();

        let one = PrimeFieldElementBig::new(1.into(), &field);
        let trace = rescue_prime_stark.trace(&one);
        let air_constraints = rescue_prime_stark.get_air_constraints(&stark.omicron);
        let hash_result = trace.last().unwrap()[0].clone();
        let boundary_constraints: Vec<BoundaryConstraint> =
            rescue_prime_stark.get_boundary_constraints(&hash_result);
        let mut proof_stream = ProofStream::default();
        let _proof = stark.prove(
            trace,
            air_constraints,
            boundary_constraints,
            &mut proof_stream,
        );
    }
}
