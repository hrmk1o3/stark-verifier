use crate::snark::hasher::HasherChip;
use crate::snark::types::{HashOut, ProofWithPublicInputs};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::Error;
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{AssignedValue, MainGateConfig};
use poseidon::Spec;

pub fn deserialize_proof(proof: String) -> ProofWithPublicInputs {
    serde_json::from_str(&proof).unwrap()
}

pub fn deserialize_public_inputs_hash(public_inputs_hash: String) -> HashOut {
    serde_json::from_str(&public_inputs_hash).unwrap()
}

pub struct TranscriptChip<N: FieldExt, const T: usize, const RATE: usize> {
    hasher_chip: HasherChip<N, T, RATE>,
}

impl<N: FieldExt, const T: usize, const RATE: usize> TranscriptChip<N, T, RATE> {
    /// Constructs the transcript chip
    pub fn new(
        ctx: &mut RegionCtx<'_, N>,
        spec: &Spec<N, T, RATE>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Error> {
        let hasher_chip = HasherChip::new(ctx, spec, main_gate_config)?;
        Ok(Self { hasher_chip })
    }

    /// Write scalar to the transcript
    pub fn write_scalar(&mut self, scalar: &AssignedValue<N>) {
        self.hasher_chip.update(&[scalar.clone()]);
    }

    /// Constrain squeezing new challenge
    pub fn squeeze(&mut self, ctx: &mut RegionCtx<'_, N>) -> Result<AssignedValue<N>, Error> {
        self.hasher_chip.hash(ctx)
    }
}

#[cfg(test)]
mod tests {
    use crate::snark::transcript::TranscriptChip;
    use halo2_proofs::{
        arithmetic::Field,
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        plonk::{Circuit, ConstraintSystem, Error},
    };
    use halo2curves::{goldilocks::fp::Goldilocks, FieldExt};
    use halo2wrong::RegionCtx;
    use halo2wrong_maingate::{mock_prover_verify, MainGate, MainGateConfig, MainGateInstructions};
    use poseidon::{Poseidon, Spec};
    use rand::rngs::OsRng;

    #[derive(Clone)]
    struct TestCircuitConfig {
        main_gate_config: MainGateConfig,
    }

    impl TestCircuitConfig {
        fn new<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
            let main_gate_config = MainGate::configure(meta);
            Self { main_gate_config }
        }
    }

    struct TestCircuit<F: FieldExt, const T: usize, const T_MINUS_ONE: usize> {
        spec: Spec<F, T, T_MINUS_ONE>,
        n: usize,
        inputs: Value<Vec<F>>,
        expected: Value<F>,
    }

    impl Circuit<Goldilocks> for TestCircuit<Goldilocks, 12, 11> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<Goldilocks>) -> Self::Config {
            TestCircuitConfig::new(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Goldilocks>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::<Goldilocks>::new(config.main_gate_config.clone());

            layouter.assign_region(
                || "",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    let mut transcript_chip = TranscriptChip::<Goldilocks, 12, 11>::new(
                        ctx,
                        &self.spec,
                        &config.main_gate_config,
                    )?;

                    for e in self.inputs.as_ref().transpose_vec(self.n) {
                        let e = main_gate.assign_value(ctx, e.map(|e| *e))?;
                        transcript_chip.write_scalar(&e);
                    }
                    let challenge = transcript_chip.squeeze(ctx)?;
                    let expected = main_gate.assign_value(ctx, self.expected)?;
                    main_gate.assert_equal(ctx, &challenge, &expected)?;

                    Ok(())
                },
            )?;

            Ok(())
        }

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }
    }

    #[test]
    fn test_poseidon() {
        let mut ref_hasher = Poseidon::<Goldilocks, 12, 8, 11>::new(8, 22);
        let spec = Spec::<Goldilocks, 12, 11>::new(8, 22);

        let inputs: Vec<Goldilocks> = (0..4).map(|_| Goldilocks::random(OsRng)).collect();

        ref_hasher.update(&inputs[..]);
        let expected = ref_hasher.squeeze(1)[0];

        let circuit = TestCircuit {
            spec,
            n: inputs.len(),
            inputs: Value::known(inputs),
            expected: Value::known(expected),
        };
        let instance = vec![vec![]];
        let _prover = MockProver::run(10, &circuit, instance).unwrap();
        _prover.assert_satisfied()
    }
}
