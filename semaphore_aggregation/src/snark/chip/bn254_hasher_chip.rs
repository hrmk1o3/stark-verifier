use std::marker::PhantomData;

use halo2_proofs::{arithmetic::FieldExt, circuit::Layouter, plonk::Error};
use halo2wrong_maingate::{
    CombinationOptionCommon, MainGate, MainGateInstructions, RegionCtx, Term,
};
use poseidon_circuit::poseidon::{primitives::Spec, PoseidonInstructions, Pow5Chip, Pow5Config, StateWord};
use snark_verifier::util::arithmetic::{fe_to_big, fe_from_big};

use crate::snark::types::assigned::AssignedFieldValue;

use super::goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig};

/// `AssignedState` is composed of `T` sized assigned values
#[derive(Debug, Clone)]
pub struct AssignedState<F: FieldExt, const STATE_WIDTH: usize>(
    pub(crate) [AssignedFieldValue<F>; STATE_WIDTH],
);

/// `HasherChip` is basically responsible for contraining permutation part of
/// transcript pipeline
#[derive(Debug, Clone)]
pub struct HasherChip<F: FieldExt, S: Spec<F, T, RATE>, const T: usize, const RATE: usize> {
    // spec: Spec<Goldilocks, T, T_MINUS_ONE>,
    hasher_config: Pow5Config<F, T, RATE>,
    goldilocks_chip_config: GoldilocksChipConfig<F>,
    _s: PhantomData<S>,
}

impl<F: FieldExt, S: Spec<F, T, RATE>, const T: usize, const RATE: usize>
    HasherChip<F, S, T, RATE>
{
    // Constructs new hasher chip with assigned initial state
    pub fn new(
        // TODO: we can remove initial state assingment in construction
        // ctx: &mut RegionCtx<'_, F>,
        // spec: &Spec<Goldilocks, T, T_MINUS_ONE>,
        hasher_config: &Pow5Config<F, T, RATE>,
        goldilocks_chip_config: &GoldilocksChipConfig<F>,
    ) -> Result<Self, Error> {
        // let goldilocks_chip = GoldilocksChip::new(goldilocks_chip_config);

        Ok(Self {
            // spec: spec.clone(),
            hasher_config: hasher_config.clone(),
            goldilocks_chip_config: goldilocks_chip_config.clone(),
            _s: PhantomData,
        })
    }

    /// Construct main gate
    pub fn goldilocks_chip(&self) -> GoldilocksChip<F> {
        GoldilocksChip::new(&self.goldilocks_chip_config)
    }

    pub fn pow5_chip(&self) -> Pow5Chip<F, T, RATE> {
        Pow5Chip::construct(self.hasher_config.clone())
    }

    pub fn main_chip(&self) -> MainGate<F> {
        MainGate::new(self.goldilocks_chip_config.main_gate_config.clone())
    }
}

const STATE_WIDTH: usize = 12;

impl<F: FieldExt, S: Spec<F, T, RATE>, const T: usize, const RATE: usize>
    HasherChip<F, S, T, RATE>
{
    /// Constrains poseidon permutation while mutating the given state
    pub fn permutation(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedState<F, STATE_WIDTH>,
    ) -> Result<AssignedState<F, STATE_WIDTH>, Error> {
        let pow5_chip = self.pow5_chip();
        let goldilocks_chip = self.goldilocks_chip();
        let main_chip = self.main_chip();

        let state = layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                // range check
                for v in input.0.iter() {
                    goldilocks_chip.assert_in_field(ctx, v)?;
                }

                let base = F::from_u128(1 << 64);
                let power_of_base = |i: u64| {
                    if i == 0 {
                        F::one()
                    } else if i == 1 {
                        base
                    } else {
                        base.pow(&[i, 0, 0, 0])
                    }
                };

                // state[j] = input[4 * j] + input[4 * j + 1] * 2^64 + input[4 * j + 2] * 2^128 + input[4 * j + 3] * 2^192 (in F)
                input.0.chunks(4).map(|chunk| {
                    assert_eq!(chunk.len(), 4);
                    let mut terms = chunk
                        .iter()
                        .enumerate()
                        .map(|(i, v)| Term::Assigned(v, power_of_base(i as u64)))
                        .collect::<Vec<_>>();
                    let state_word_value = Term::compose(&terms, F::zero());
                    terms.push(Term::unassigned_to_sub(state_word_value));
                    let state_word = main_chip
                        .apply(
                            ctx,
                            terms,
                            F::zero(),
                            CombinationOptionCommon::OneLinerAdd.into(),
                        )?
                        .swap_remove(4);

                    Ok(state_word.into())
                }).collect::<Result<Vec<StateWord<F>>, Error>>()
            },
        )?;
        let new_state = PoseidonInstructions::<F, S, T, RATE>::permute(
            &pow5_chip,
            layouter,
            &state.try_into().unwrap(),
        )?;

        let output = layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                let output = new_state
                    .iter()
                    .map(|limb| {
                        let modulus = goldilocks_chip.goldilocks_modulus();
                        let (state012, state3) = limb
                            .0
                            .value()
                            .map(|value| {
                                let mut value = fe_to_big(*value);
                                let state0 = fe_from_big::<F>(value.clone() % modulus.clone());
                                value /= modulus.clone();
                                let state1 = fe_from_big::<F>(value.clone() % modulus.clone());
                                value /= modulus.clone();
                                let state2 = fe_from_big::<F>(value.clone() % modulus.clone());
                                value /= modulus.clone();
                                let state3 = fe_from_big::<F>(value % modulus.clone());

                                (((state0, state1), state2), state3)
                            })
                            .unzip();
                        let (state01, state2) = state012.unzip();
                        let (state0, state1) = state01.unzip();

                        let terms = vec![
                            Term::Unassigned(state0, F::one()),
                            Term::Unassigned(state1, fe_from_big::<F>(modulus.clone())),
                            Term::Unassigned(
                                state2,
                                fe_from_big::<F>(modulus.pow(2)),
                            ),
                            Term::Unassigned(
                                state3,
                                fe_from_big::<F>(modulus.pow(3)),
                            ),
                            Term::assigned_to_sub(&limb.0)
                        ];
                        let mut state = main_chip.apply(
                            ctx,
                            terms,
                            F::zero(),
                            CombinationOptionCommon::OneLinerAdd.into(),
                        )?;
                        state.pop();
                        // for v in state.iter() {
                        //     dbg!(v.value());
                        // }

                        let state = state
                            .into_iter()
                            .map(AssignedFieldValue::from)
                            .collect::<Vec<_>>();

                        Ok(state)
                    })
                    .collect::<Result<Vec<_>, Error>>()?
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();

                // range check
                for v in output.iter() {
                    goldilocks_chip.assert_in_field(ctx, v)?;
                }

                Ok(output)
            },
        )?;

        let output  = AssignedState(output.try_into().unwrap());

        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::{floor_planner::V1, *},
        dev::MockProver,
        halo2curves::bn256::Fr,
        plonk::*, arithmetic::Field,
    };
    use halo2curves::goldilocks::fp::Goldilocks;
    use plonky2::{
        field::{
            goldilocks_field::GoldilocksField,
            types::{Field as Plonky2Field, PrimeField64},
        },
        hash::hashing::PlonkyPermutation,
    };
    use poseidon_circuit::poseidon::primitives::P128Pow5T3;

    use crate::snark::{
        config::PoseidonBN128Permutation, verifier_circuit::MainGateWithRangeConfig,
    };

    use super::*;

    #[derive(Default)]
    pub struct Bn254PoseidonPermutationCircuit {
        pub input: [Goldilocks; STATE_WIDTH],
        pub output: [Goldilocks; STATE_WIDTH],
    }

    impl Bn254PoseidonPermutationCircuit {
        pub fn new(input: [Goldilocks; STATE_WIDTH]) -> Self {
            let mut hasher = PoseidonBN128Permutation::new(std::iter::repeat(Default::default()));
            hasher.set_from_slice(&input.map(|v| GoldilocksField::from_canonical_u64(v.0)), 0);
            hasher.permute();
            let output = hasher.state.map(|v| Goldilocks(v.to_canonical_u64()));

            Self { input, output }
        }

        pub fn degree_bits(&self) -> u32 {
            if cfg!(feature = "not-constrain-range-check") {
                6
            } else {
                7
            }
        }

        pub fn instance(&self) -> Vec<Vec<Fr>> {
            let first_column = self
                .output
                .map(|v| fe_from_big::<Fr>(fe_to_big::<Goldilocks>(v)))
                .to_vec();

            vec![first_column]
        }
    }

    #[derive(Clone)]
    pub struct Bn254PoseidonPermutationConfig {
        pub goldilocks_chip_config: GoldilocksChipConfig<Fr>,
        pub hasher_config: Pow5Config<Fr, 3, 2>,
    }

    impl Circuit<Fr> for Bn254PoseidonPermutationCircuit {
        type Config = Bn254PoseidonPermutationConfig;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let main_gate_config = MainGateWithRangeConfig::new(meta);
            let goldilocks_chip_config = GoldilocksChip::configure(&main_gate_config.main_gate_config);
            // let hasher_config = Pow5Chip::<Fr, 3, 2>::configure(&main_gate_config);
            let state = (0..3).map(|_| meta.advice_column()).collect::<Vec<_>>();
            let hasher_config = {
                let partial_sbox = meta.advice_column();
    
                let rc_a = (0..3).map(|_| meta.fixed_column()).collect::<Vec<_>>();
                let rc_b = (0..3).map(|_| meta.fixed_column()).collect::<Vec<_>>();
    
                meta.enable_constant(rc_b[0]);
    
                Pow5Chip::configure::<P128Pow5T3<Fr>>(
                    meta,
                    state.try_into().unwrap(),
                    partial_sbox,
                    rc_a.try_into().unwrap(),
                    rc_b.try_into().unwrap(),
                )
            };

            Bn254PoseidonPermutationConfig { goldilocks_chip_config, hasher_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::new(config.goldilocks_chip_config.main_gate_config.clone());
            let goldilocks_chip = GoldilocksChip::new(&config.goldilocks_chip_config);
            let hasher_chip = HasherChip::<Fr, P128Pow5T3<Fr>, 3, 2>::new(
                &config.hasher_config,
                &config.goldilocks_chip_config,
            )?;

            let input_assigned = layouter.assign_region(
                || "addition in the Goldilocks field",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);

                    self.input
                        .iter()
                        .map(|value| goldilocks_chip.assign_value(ctx, Value::known(*value)))
                        .collect::<Result<Vec<_>, Error>>()
                },
            )?;

            let output_assigned = hasher_chip.permutation(&mut layouter, AssignedState(input_assigned.try_into().unwrap()))?;

            layouter.assign_region(
                || "addition in the Goldilocks field",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);

                    for (expected_value, actual_assigned) in self.output.iter().zip(output_assigned.0.iter()) {
                        let expected_assigned =
                            goldilocks_chip.assign_constant(ctx, *expected_value)?;
                        main_gate.assert_equal(ctx, actual_assigned, &expected_assigned)?;
                    }

                    Ok(())
                },
            )?;

            for (row, v) in output_assigned.0.iter().enumerate() {
                main_gate.expose_public(layouter.namespace(|| format!("public input {row}")), v.value.clone(), row)?;
            }

            Ok(())
        }
    }

    #[test]
    fn test_bn254_permutation_circuit() {
        let mut input = [Goldilocks::zero(); STATE_WIDTH];
        input[0] = Goldilocks::from(1u64);
        input[4] = Goldilocks::from(2u64);
        let circuit = Bn254PoseidonPermutationCircuit::new(input);
        let instance = circuit.instance();
        let k = circuit.degree_bits();

        // runs mock prover
        let mock_prover = MockProver::run(k, &circuit, instance).unwrap();
        mock_prover.assert_satisfied();
    }
}
