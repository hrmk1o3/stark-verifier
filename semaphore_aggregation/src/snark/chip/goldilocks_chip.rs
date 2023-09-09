use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::Field,
    circuit::Value,
    plonk::Error,
};
use halo2curves::{goldilocks::fp::Goldilocks, FieldExt};
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{
    big_to_fe, decompose, fe_to_big, power_of_two, AssignedCondition,
    CombinationOptionCommon, MainGate, MainGateConfig, MainGateInstructions, Term,
};
use itertools::Itertools;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Num, Zero};

use crate::snark::types::assigned::AssignedFieldValue;

// TODO : range check
#[derive(Clone, Debug)]
pub struct GoldilocksChipConfig<F: FieldExt> {
    pub main_gate_config: MainGateConfig,
    _marker: PhantomData<F>,
}

pub struct GoldilocksChip<F: FieldExt> {
    goldilocks_chip_config: GoldilocksChipConfig<F>,
}

impl<F: FieldExt> GoldilocksChip<F> {
    pub fn configure(main_gate_config: &MainGateConfig) -> GoldilocksChipConfig<F> {
        GoldilocksChipConfig {
            main_gate_config: main_gate_config.clone(),
            _marker: PhantomData,
        }
    }

    pub fn new(goldilocks_chip_config: &GoldilocksChipConfig<F>) -> Self {
        Self {
            goldilocks_chip_config: goldilocks_chip_config.clone(),
        }
    }

    fn main_gate(&self) -> MainGate<F> {
        MainGate::new(self.goldilocks_chip_config.main_gate_config.clone())
    }

    pub fn goldilocks_modulus(&self) -> BigUint {
        BigUint::from_str_radix(&Goldilocks::MODULUS[2..], 16).unwrap()
    }

    pub fn goldilocks_to_native_fe(&self, goldilocks: Goldilocks) -> F {
        big_to_fe::<F>(fe_to_big::<Goldilocks>(goldilocks))
    }

    // assumes `fe` is already in goldilocks field
    fn native_fe_to_goldilocks(&self, fe: F) -> Goldilocks {
        big_to_fe::<Goldilocks>(fe_to_big::<F>(fe))
    }

    // XXX: Check range in the Goldilocks field.
    pub fn assign_value(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        unassigned: Value<F>,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let main_gate = self.main_gate();
        Ok(main_gate.assign_value(ctx, unassigned)?.into())
    }

    pub fn assign_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        constant: Goldilocks,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let constant: F = big_to_fe(fe_to_big::<Goldilocks>(constant));
        self.assign_value(ctx, Value::known(constant)) // XXX: fixed value になっていない
    }

    // XXX: Check range in the Goldilocks field.
    pub fn add(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedFieldValue<F>,
        rhs: &AssignedFieldValue<F>,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let (quotient, remainder) = lhs
            .value()
            .zip(rhs.value())
            .map(|(l, r)| {
                let (q, r) = (fe_to_big(*l) + fe_to_big(*r)).div_rem(&goldilocks_modulus);
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        Ok(main_gate
            .apply(
                ctx,
                [
                    Term::assigned_to_add(lhs),
                    Term::assigned_to_add(rhs),
                    Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus)),
                    Term::unassigned_to_sub(remainder),
                ],
                F::zero(),
                CombinationOptionCommon::OneLinerAdd.into(),
            )?
            .swap_remove(3).into())
    }

    // XXX: Check range in the Goldilocks field.
    pub fn sub(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedFieldValue<F>,
        rhs: &AssignedFieldValue<F>,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let (quotient, remainder) = lhs
            .value()
            .zip(rhs.value())
            .map(|(l, r)| {
                let (q, r) = (fe_to_big(*l) + goldilocks_modulus.clone() - fe_to_big(*r))
                    .div_rem(&goldilocks_modulus.clone());
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        Ok(main_gate
            .apply(
                ctx,
                [
                    Term::assigned_to_add(lhs),
                    Term::unassigned_to_add(Value::known(big_to_fe(goldilocks_modulus.clone()))),
                    Term::assigned_to_sub(rhs),
                    Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus.clone())),
                    Term::unassigned_to_sub(remainder),
                ],
                F::zero(),
                CombinationOptionCommon::OneLinerAdd.into(),
            )?
            .swap_remove(4).into())
    }

    // XXX: Check range in the Goldilocks field.
    pub fn mul(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedFieldValue<F>,
        rhs: &AssignedFieldValue<F>,
    ) -> Result<AssignedFieldValue<F>, Error> {
        self.mul_with_constant(ctx, lhs, rhs, Goldilocks::one())
    }

    // XXX: Check range in the Goldilocks field.
    /// Assigns a new witness `r` as:
    /// `lhs * rhs * constant - p * q - r = 0`
    pub fn mul_with_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedFieldValue<F>,
        rhs: &AssignedFieldValue<F>,
        constant: Goldilocks,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let constant = self.goldilocks_to_native_fe(constant);
        let (quotient, remainder) = lhs
            .value()
            .zip(rhs.value())
            .map(|(l, r)| {
                let (q, r) = (fe_to_big(*l) * fe_to_big(*r) * fe_to_big(constant))
                    .div_rem(&goldilocks_modulus);
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        Ok(main_gate
            .apply(
                ctx,
                [
                    Term::assigned_to_mul(lhs),
                    Term::assigned_to_mul(rhs),
                    Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus)),
                    Term::unassigned_to_sub(remainder),
                ],
                F::zero(),
                CombinationOptionCommon::CombineToNextScaleMul(F::zero(), constant).into(),
            )?
            .swap_remove(3).into())
    }

    // XXX: Check range in the Goldilocks field.
    pub fn mul_add_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedFieldValue<F>,
        b: &AssignedFieldValue<F>,
        to_add: Goldilocks,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let to_add = self.goldilocks_to_native_fe(to_add);
        let (quotient, remainder) = a
            .value()
            .zip(b.value())
            .map(|(l, r)| {
                let (q, r) = (fe_to_big(*l) * fe_to_big(*r) + fe_to_big(to_add))
                    .div_rem(&goldilocks_modulus);
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        Ok(main_gate
            .apply(
                ctx,
                [
                    Term::assigned_to_mul(a),
                    Term::assigned_to_mul(b),
                    Term::unassigned_to_add(Value::known(to_add)),
                    Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus)),
                    Term::unassigned_to_sub(remainder),
                ],
                F::zero(),
                CombinationOptionCommon::OneLinerMul.into(),
            )?
            .swap_remove(4).into())
    }

    // XXX: Check range in the Goldilocks field.
    pub fn add_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedFieldValue<F>,
        constant: Goldilocks,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let (quotient, remainder) = a
            .value()
            .zip(Value::known(self.goldilocks_to_native_fe(constant)))
            .map(|(l, r)| {
                let (q, r) = (fe_to_big(*l) + fe_to_big(r)).div_rem(&goldilocks_modulus);
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        Ok(main_gate
            .apply(
                ctx,
                [
                    Term::assigned_to_add(a),
                    Term::unassigned_to_add(Value::known(self.goldilocks_to_native_fe(constant))),
                    Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus)),
                    Term::unassigned_to_sub(remainder),
                ],
                F::zero(),
                CombinationOptionCommon::OneLinerAdd.into(),
            )?
            .swap_remove(3).into())
    }

    /// This function checks if `lhs` is the same as `rhs` in `F` (not the Goldilocks field).
    // TODO: Checks if `lhs` is the same as `rhs` in the Goldilocks field.
    pub fn assert_equal(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedFieldValue<F>,
        rhs: &AssignedFieldValue<F>,
    ) -> Result<(), Error> {
        let main_gate = self.main_gate();
        let lhs_minus_rhs = self.sub(ctx, lhs, rhs)?;
        main_gate.assert_zero(ctx, &lhs_minus_rhs)
    }

    pub fn assert_one(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedFieldValue<F>,
    ) -> Result<(), Error> {
        let one = self.assign_constant(ctx, Goldilocks::one())?;
        self.assert_equal(ctx, a, &one)
    } // OK

    pub fn assert_zero(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedFieldValue<F>,
    ) -> Result<(), Error> {
        let zero = self.assign_constant(ctx, Goldilocks::zero())?;
        self.assert_equal(ctx, a, &zero)
    } // OK

    // XXX: Check range in the Goldilocks field.
    // TODO : optimize, underconstrained?
    pub fn compose(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        terms: &[Term<F>],
        constant: Goldilocks,
    ) -> Result<AssignedFieldValue<F>, Error> {
        assert!(!terms.is_empty(), "At least one term is expected");
        let goldilocks_modulus = self.goldilocks_modulus();
        let composed = terms.iter().fold(
            Value::known(self.goldilocks_to_native_fe(constant)),
            |acc, term| {
                acc.zip(term.coeff()).map(|(acc, coeff)| {
                    let (_, remainder) = (fe_to_big(acc)
                        + fe_to_big(coeff) * fe_to_big(term.base()))
                    .div_rem(&goldilocks_modulus);
                    big_to_fe(remainder)
                })
            },
        );
        let composed = self.assign_value(ctx, composed)?;
        Ok(composed)
    }

    fn assign_bit(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bit: Value<F>,
    ) -> Result<AssignedCondition<F>, Error> {
        let main_gate = self.main_gate();
        main_gate.assign_bit(ctx, bit)
    }

    // XXX: Check range in the Goldilocks field.
    /// This function returns a pair of values (a', r) such that
    /// If 0 < a < Goldilocks::MODULUS, then r = 0 and a' = a^(-1) mod Goldilocks::MODULUS.
    /// If a = 0, then r = 1 and a' = 1.
    pub fn invert(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedFieldValue<F>,
    ) -> Result<(AssignedFieldValue<F>, AssignedCondition<F>), Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let (one, zero) = (Goldilocks::one(), Goldilocks::zero());

        // `r` means whether `a` is zero or not.
        // First enforce `r` to be a bit
        // (a * a') - 1 + r = p * q
        // r * a' - r = 0
        // if r = 1 then a' = 1
        // if r = 0 then a' = 1/a

        // Witness layout:
        // | A | B  | C |
        // | - | -- | - |
        // | a | a' | r |
        // | r | a' | r |

        let (r, a_inv) = a
            .value()
            .map(|a| {
                Option::from(self.native_fe_to_goldilocks(*a).invert())
                    .map(|a_inverted| {
                        (
                            self.goldilocks_to_native_fe(zero),
                            self.goldilocks_to_native_fe(a_inverted),
                        )
                    })
                    .unwrap_or_else(|| {
                        (
                            self.goldilocks_to_native_fe(one),
                            self.goldilocks_to_native_fe(one),
                        )
                    })
            })
            .unzip();

        let r = self.assign_bit(ctx, r)?;

        // (a * a') - 1 + r = p * q
        let quotient = a
            .value()
            .zip(a_inv)
            .zip(r.value())
            .map(|((&a, a_inv), &r)| {
                let (q, r) = (fe_to_big(a * a_inv - F::one() + r)).div_rem(&goldilocks_modulus);
                assert_eq!(r, BigUint::zero());
                big_to_fe::<F>(q)
            });

        let a_inv = main_gate
            .apply(
                ctx,
                [
                    Term::assigned_to_mul(a),
                    Term::unassigned_to_mul(a_inv),
                    Term::unassigned_to_sub(Value::known(self.goldilocks_to_native_fe(one))),
                    Term::assigned_to_add(&r),
                    Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus)),
                ],
                F::zero(),
                CombinationOptionCommon::OneLinerMul.into(),
            )?
            .swap_remove(1);

        // r * a' - r = 0
        main_gate.apply(
            ctx,
            [
                Term::assigned_to_mul(&r),
                Term::assigned_to_mul(&a_inv),
                Term::assigned_to_sub(&r),
            ],
            F::zero(),
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok((a_inv.into(), r))
    }

    // NOTICE: Assume `a` and `b` are in the Goldilocks field.
    // TODO : is it okay?
    pub fn select(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedFieldValue<F>,
        b: &AssignedFieldValue<F>,
        cond: &AssignedCondition<F>,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let main_gate = self.main_gate();
        Ok(main_gate.select(ctx, &a, &b, cond)?.into())
    }

    pub fn is_zero(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedFieldValue<F>,
    ) -> Result<AssignedCondition<F>, Error> {
        let (_, is_zero) = self.invert(ctx, a)?;
        Ok(is_zero)
    } // OK

    /// Assigns array values of bit values which is equal to decomposition of
    /// given assigned value
    pub fn to_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        composed: &AssignedFieldValue<F>,
        number_of_bits: usize,
    ) -> Result<Vec<AssignedCondition<F>>, Error> {
        assert!(number_of_bits <= F::NUM_BITS as usize);

        let decomposed_value = composed.value().map(|value| {
            decompose(self.native_fe_to_goldilocks(*value), number_of_bits, 1)
                .iter()
                .map(|v| self.goldilocks_to_native_fe(*v))
                .collect::<Vec<F>>()
        });

        let (bits, bases): (Vec<_>, Vec<_>) = (0..number_of_bits)
            .map(|i| {
                let bit = decomposed_value.as_ref().map(|bits| bits[i]);
                let bit = self.assign_bit(ctx, bit)?;
                let base = power_of_two::<F>(i);
                Ok((bit, base))
            })
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .unzip();

        let terms = bits
            .iter()
            .zip(bases.into_iter())
            .map(|(bit, base)| Term::Assigned(bit, base))
            .collect::<Vec<_>>();
        let result = self.compose(ctx, &terms, Goldilocks::zero())?;
        self.assert_equal(ctx, &result, composed)?;
        Ok(bits)
    }

    pub fn range_check(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedFieldValue<F>,
        n_log: usize,
    ) -> Result<(), Error> {
        let _ = self.to_bits(ctx, x, n_log as usize)?;

        Ok(())
    }

    /// Asserts that `x`'s big-endian bit representation has at least `leading_zeros` leading zeros.
    pub(crate) fn assert_leading_zeros(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedFieldValue<F>,
        leading_zeros: u32,
    ) -> Result<(), Error> {
        self.range_check(ctx, x, (64 - leading_zeros) as usize)
    } // OK

    pub fn from_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bits: &Vec<AssignedCondition<F>>,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let terms = bits
            .iter()
            .enumerate()
            .map(|(i, bit)| Term::Assigned(bit, power_of_two(i)))
            .collect_vec();
        self.compose(ctx, &terms[..], Goldilocks::zero())
    }

    pub fn exp_power_of_2(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedFieldValue<F>,
        power_log: usize,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let mut result = a.clone();
        for _ in 0..power_log {
            result = self.mul(ctx, &result, &result)?;
        }
        Ok(result)
    } // OK

    pub fn exp_from_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        base: Goldilocks,
        power_bits: &[AssignedCondition<F>],
    ) -> Result<AssignedFieldValue<F>, Error> {
        let main_gate = self.main_gate();
        let mut x = self.assign_constant(ctx, Goldilocks::one())?.into();
        let one = self.assign_constant(ctx, Goldilocks::one())?.into();
        for (i, bit) in power_bits.iter().enumerate() {
            let is_zero_bit = main_gate.is_zero(ctx, bit)?;

            let power = u64::from(1u64 << i).to_le();
            let base = self.assign_constant(ctx, base.pow(&[power, 0, 0, 0]))?;
            let multiplicand = self.select(ctx, &one, &base, &is_zero_bit)?;
            x = self.mul(ctx, &x, &multiplicand)?;
        }
        Ok(x)
    } // OK

    pub fn is_equal(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedFieldValue<F>,
        b: &AssignedFieldValue<F>,
    ) -> Result<AssignedCondition<F>, Error> {
        let a_mimus_b = self.sub(ctx, a, b)?;
        self.is_zero(ctx, &a_mimus_b)
    } // OK
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use halo2_proofs::{
        circuit::{floor_planner::V1, *},
        dev::MockProver,
        halo2curves::bn256::Fr,
        plonk::*,
    };
    use halo2curves::group::ff::PrimeField;

    use crate::snark::verifier_circuit::MainGateWithRangeConfig;

    use super::*;

    #[derive(Default)]
    pub struct GoldilocksAdditionCircuit {
        pub a: Goldilocks,
        pub b: Goldilocks,
        pub c: Goldilocks,
    }

    impl GoldilocksAdditionCircuit {
        pub fn new(a: Goldilocks, b: Goldilocks) -> Self {
            let c = a + b;

            Self { a, b, c }
        }

        pub fn degree_bits(&self) -> u32 {
            12
        }

        pub fn instance(&self) -> Vec<Vec<Fr>> {
            let first_column = [self.c]
                .map(|v| big_to_fe::<Fr>(fe_to_big::<Goldilocks>(v)))
                .to_vec();

            vec![first_column]
        }
    }

    impl Circuit<Fr> for GoldilocksAdditionCircuit {
        type Config = MainGateWithRangeConfig<Fr>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            MainGateWithRangeConfig::new(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::new(config.main_gate_config.clone());
            let goldilocks_chip_config = GoldilocksChip::configure(&config.main_gate_config);

            let a = big_to_fe::<Fr>(fe_to_big::<Goldilocks>(self.a));
            let b = big_to_fe::<Fr>(fe_to_big::<Goldilocks>(self.b));
            let c = big_to_fe::<Fr>(fe_to_big::<Goldilocks>(self.c));

            let c_assigned = layouter.assign_region(
                || "addition in the Goldilocks field",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    let goldilocks_chip = GoldilocksChip::new(&goldilocks_chip_config);
                    let a_assigned = goldilocks_chip.assign_value(ctx, Value::known(a))?;
                    let b_assigned = goldilocks_chip.assign_value(ctx, Value::known(b))?;
                    let c_assigned = goldilocks_chip.add(ctx, &a_assigned, &b_assigned)?;

                    let expected_c_assigned = goldilocks_chip.assign_value(ctx, Value::known(c))?;
                    main_gate.assert_equal(ctx, &c_assigned, &expected_c_assigned)?;

                    Ok(c_assigned)
                },
            )?;

            main_gate.expose_public(layouter, (*c_assigned).clone(), 0)?;

            Ok(())
        }
    }

    #[test]
    fn test_add_circuit() {
        let a = Goldilocks::from(1u64);
        let b = Goldilocks::from(2u64);
        // let c = Goldilocks::from(3u64);
        let circuit = GoldilocksAdditionCircuit::new(a, b);
        let instance = circuit.instance();
        let k = circuit.degree_bits();

        // runs mock prover
        let mock_prover = MockProver::run(k, &circuit, instance).unwrap();
        mock_prover.assert_satisfied();
    }

    #[derive(Default)]
    pub struct GoldilocksDecomposeCircuit<const NUM_BITS: usize> {
        pub a: Goldilocks,
    }

    impl<const NUM_BITS: usize> GoldilocksDecomposeCircuit<NUM_BITS> {
        pub fn new(a: Goldilocks) -> Self {
            assert!(NUM_BITS <= Goldilocks::NUM_BITS as usize);

            // let mut decomposed_a = decompose(a, Goldilocks::NUM_BITS as usize, 1);
            // for limb in decomposed_a.drain(NUM_BITS..) {
            //     assert_eq!(limb, Goldilocks::zero());
            // }

            Self {
                a,
            }
        }

        pub fn degree_bits(&self) -> u32 {
            12
        }

        pub fn instance(&self) -> Vec<Vec<Fr>> {
            let first_column = [self.a]
                .map(|v| big_to_fe::<Fr>(fe_to_big::<Goldilocks>(v)))
                .to_vec();

            vec![first_column]
        }
    }

    impl<const NUM_BITS: usize> Circuit<Fr> for GoldilocksDecomposeCircuit<NUM_BITS> {
        type Config = MainGateWithRangeConfig<Fr>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            MainGateWithRangeConfig::new(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::new(config.main_gate_config.clone());
            let goldilocks_chip_config = GoldilocksChip::configure(&config.main_gate_config);

            let a = Value::known(big_to_fe::<Fr>(fe_to_big::<Goldilocks>(self.a)));

            let a_assigned = layouter.assign_region(
                || "addition in the Goldilocks field",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    let goldilocks_chip = GoldilocksChip::new(&goldilocks_chip_config);
                    let a_assigned = goldilocks_chip.assign_value(ctx, a)?;
                    let decomposed_a_assigned = goldilocks_chip.to_bits(ctx, &a_assigned, NUM_BITS)?;
                    main_gate.assert_one(ctx, &decomposed_a_assigned[63])?;

                    Ok(a_assigned)
                },
            )?;

            main_gate.expose_public(layouter, (*a_assigned).clone(), 0)?;

            Ok(())
        }
    }

    #[test]
    fn test_to_bits_circuit() {
        let a = Goldilocks::from(105u64);
        let circuit = GoldilocksDecomposeCircuit::<7>::new(a);
        let instance = circuit.instance();
        let k = circuit.degree_bits();

        // runs mock prover
        let mock_prover = MockProver::run(k, &circuit, instance).unwrap();
        mock_prover.assert_satisfied();
    }

    // XXX: should panic?
    #[test]
    fn test_to_bits_circuit_overflow() {
        let a = Goldilocks::from(u64::MAX - 4);
        let circuit = GoldilocksDecomposeCircuit::<64>::new(a);
        let instance = circuit.instance();
        let k = circuit.degree_bits();

        // runs mock prover
        let mock_prover = MockProver::run(k, &circuit, instance).unwrap();
        mock_prover.assert_satisfied();
    }

    #[test]
    #[should_panic]
    fn test_panic_to_bits_circuit() {
        let a = Goldilocks::from(105u64);
        let circuit = GoldilocksDecomposeCircuit::<6>::new(a);
        let instance = circuit.instance();
        let k = circuit.degree_bits();

        // runs mock prover
        let mock_prover = MockProver::run(k, &circuit, instance).unwrap();
        mock_prover.assert_satisfied();
    }
}
