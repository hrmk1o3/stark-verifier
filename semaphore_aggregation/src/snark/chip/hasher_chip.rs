use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    plonk::Error,
};
use halo2curves::goldilocks::fp::Goldilocks;
use halo2wrong_maingate::{RegionCtx, Term};
use poseidon::{SparseMDSMatrix, Spec, State};

use crate::snark::types::assigned::AssignedFieldValue;

use super::goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig};

/// `AssignedState` is composed of `T` sized assigned values
#[derive(Debug, Clone)]
pub struct AssignedState<F: FieldExt, const T: usize>(pub(super) [AssignedFieldValue<F>; T]);

/// `HasherChip` is basically responsible for contraining permutation part of
/// transcript pipeline
#[derive(Debug, Clone)]
pub struct HasherChip<F: FieldExt, const T: usize, const T_MINUS_ONE: usize, const RATE: usize> {
    state: AssignedState<F, T>,
    absorbing: Vec<AssignedFieldValue<F>>,
    output_buffer: Vec<AssignedFieldValue<F>>,
    spec: Spec<Goldilocks, T, T_MINUS_ONE>,
    goldilocks_chip_config: GoldilocksChipConfig<F>,
}

impl<F: FieldExt, const T: usize, const T_MINUS_ONE: usize, const RATE: usize>
    HasherChip<F, T, T_MINUS_ONE, RATE>
{
    // Constructs new hasher chip with assigned initial state
    pub fn new(
        // TODO: we can remove initial state assingment in construction
        ctx: &mut RegionCtx<'_, F>,
        spec: &Spec<Goldilocks, T, T_MINUS_ONE>,
        goldilocks_chip_config: &GoldilocksChipConfig<F>,
    ) -> Result<Self, Error> {
        let goldilocks_chip = GoldilocksChip::new(goldilocks_chip_config);

        let initial_state = State::<_, T>::default()
            .words()
            .iter()
            .map(|word| goldilocks_chip.assign_constant(ctx, *word))
            .collect::<Result<Vec<_>, Error>>()?;

        Ok(Self {
            state: AssignedState(initial_state.try_into().unwrap()),
            spec: spec.clone(),
            absorbing: vec![],
            output_buffer: vec![],
            goldilocks_chip_config: goldilocks_chip_config.clone(),
        })
    }

    /// Appends field elements to the absorbation line. It won't perform
    /// permutation here
    pub fn update(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        element: &AssignedFieldValue<F>,
    ) -> Result<(), Error> {
        self.output_buffer.clear();
        self.absorbing.push(element.clone());
        Ok(())
    }

    fn absorb_buffered_inputs(&mut self, ctx: &mut RegionCtx<'_, F>) -> Result<(), Error> {
        if self.absorbing.is_empty() {
            return Ok(());
        }
        let buffered_inputs = self.absorbing.clone();
        for input_chunk in buffered_inputs.chunks(RATE) {
            self.duplexing(ctx, input_chunk)?;
        }
        self.absorbing.clear();
        Ok(())
    }

    pub fn squeeze(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        num_outputs: usize,
    ) -> Result<Vec<AssignedFieldValue<F>>, Error> {
        let mut output = vec![];
        for _i in 0..num_outputs {
            self.absorb_buffered_inputs(ctx)?;

            if self.output_buffer.is_empty() {
                self.permutation(ctx)?;
                self.output_buffer = self.state.0[0..RATE].to_vec();
            }
            output.push(self.output_buffer.pop().unwrap())
        }
        Ok(output)
    }
}

impl<F: FieldExt, const T: usize, const T_MINUS_ONE: usize, const RATE: usize>
    HasherChip<F, T, T_MINUS_ONE, RATE>
{
    /// Construct main gate
    pub fn goldilocks_chip(&self) -> GoldilocksChip<F> {
        GoldilocksChip::new(&self.goldilocks_chip_config)
    }

    /*
        Internally expose poseidion parameters and matrices
    */

    pub(super) fn r_f_half(&self) -> usize {
        self.spec.r_f() / 2
    }

    pub(super) fn constants_start(&self) -> Vec<[Goldilocks; T]> {
        self.spec.constants().start().clone()
    }

    pub(super) fn constants_partial(&self) -> Vec<Goldilocks> {
        self.spec.constants().partial().clone()
    }

    pub(super) fn constants_end(&self) -> Vec<[Goldilocks; T]> {
        self.spec.constants().end().clone()
    }

    pub(super) fn mds(&self) -> [[Goldilocks; T]; T] {
        self.spec.mds_matrices().mds().rows()
    }

    pub(super) fn pre_sparse_mds(&self) -> [[Goldilocks; T]; T] {
        self.spec.mds_matrices().pre_sparse_mds().rows()
    }

    pub(super) fn sparse_matrices(&self) -> Vec<SparseMDSMatrix<Goldilocks, T, T_MINUS_ONE>> {
        self.spec.mds_matrices().sparse_matrices().clone()
    }
}

impl<F: FieldExt, const T: usize, const T_MINUS_ONE: usize, const RATE: usize>
    HasherChip<F, T, T_MINUS_ONE, RATE>
{
    /// Applies full state sbox then adds constants to each word in the state
    fn sbox_full(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        constants: &[Goldilocks; T],
    ) -> Result<(), Error> {
        let goldilocks_chip = self.goldilocks_chip();
        for (word, constant) in self.state.0.iter_mut().zip(constants.iter()) {
            let word2 = goldilocks_chip.mul(ctx, word, word)?;
            let word4 = goldilocks_chip.mul(ctx, &word2, &word2)?;
            let word6 = goldilocks_chip.mul(ctx, &word2, &word4)?;
            *word = goldilocks_chip.mul_add_constant(ctx, &word6, word, *constant)?;
        }
        Ok(())
    }

    /// Applies sbox to the first word then adds constants to each word in the
    /// state
    fn sbox_part(&mut self, ctx: &mut RegionCtx<'_, F>, constant: Goldilocks) -> Result<(), Error> {
        let goldilocks_chip = self.goldilocks_chip();
        let word = &mut self.state.0[0];
        let word2 = goldilocks_chip.mul(ctx, word, word)?;
        let word4 = goldilocks_chip.mul(ctx, &word2, &word2)?;
        let word6 = goldilocks_chip.mul(ctx, &word2, &word4)?;
        *word = goldilocks_chip.mul_add_constant(ctx, &word6, word, constant)?;

        Ok(())
    }

    // Adds pre constants to the state.
    fn absorb_with_pre_constants(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        pre_constants: &[Goldilocks; T],
    ) -> Result<(), Error> {
        let goldilocks_chip = self.goldilocks_chip();

        // Add pre constants
        for (word, constant) in self.state.0.iter_mut().zip(pre_constants.iter()) {
            *word = goldilocks_chip.add_constant(ctx, word, *constant)?;
        }

        Ok(())
    }

    /// Applies MDS State multiplication
    fn apply_mds(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        mds: &[[Goldilocks; T]; T],
    ) -> Result<(), Error> {
        let goldilocks_chip = self.goldilocks_chip();
        // Calculate new state
        let new_state = mds
            .iter()
            .map(|row| {
                // term_i = s_0 * e_i_0 + s_1 * e_i_1 + ....
                let terms = self
                    .state
                    .0
                    .iter()
                    .zip(row.iter())
                    .map(|(e, word)| {
                        Term::Assigned(e, goldilocks_chip.goldilocks_to_native_fe(*word))
                    })
                    .collect::<Vec<Term<F>>>();

                goldilocks_chip.compose(ctx, &terms[..], Goldilocks::zero())
            })
            .collect::<Result<Vec<_>, Error>>()?;

        // Assign new state
        for (word, new_word) in self.state.0.iter_mut().zip(new_state.into_iter()) {
            *word = new_word
        }

        Ok(())
    }

    /// Applies sparse MDS to the state
    fn apply_sparse_mds(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        mds: &SparseMDSMatrix<Goldilocks, T, T_MINUS_ONE>,
    ) -> Result<(), Error> {
        let goldilocks_chip = self.goldilocks_chip();
        // For the 0th word
        let terms = self
            .state
            .0
            .iter()
            .zip(mds.row().iter())
            .map(|(e, word)| Term::Assigned(e, goldilocks_chip.goldilocks_to_native_fe(*word)))
            .collect::<Vec<Term<F>>>();
        let mut new_state =
            vec![self
                .goldilocks_chip()
                .compose(ctx, &terms[..], Goldilocks::zero())?];

        // Rest of the trainsition ie the sparse part
        for (e, word) in mds.col_hat().iter().zip(self.state.0.iter().skip(1)) {
            new_state.push(goldilocks_chip.compose(
                ctx,
                &[
                    Term::Assigned(
                        &self.state.0[0],
                        goldilocks_chip.goldilocks_to_native_fe(*e),
                    ),
                    Term::Assigned(word, F::one()),
                ],
                Goldilocks::zero(),
            )?);
        }

        // Assign new state
        for (word, new_word) in self.state.0.iter_mut().zip(new_state.into_iter()) {
            *word = new_word
        }

        Ok(())
    }

    /// Constrains poseidon permutation while mutating the given state
    pub fn permutation(&mut self, ctx: &mut RegionCtx<'_, F>) -> Result<(), Error> {
        let r_f = self.r_f_half();
        let mds = self.mds();
        let pre_sparse_mds = self.pre_sparse_mds();
        let sparse_matrices = self.sparse_matrices();

        // First half of the full rounds
        let constants = self.constants_start();
        self.absorb_with_pre_constants(ctx, &constants[0])?;
        for constants in constants.iter().skip(1).take(r_f - 1) {
            self.sbox_full(ctx, constants)?;
            self.apply_mds(ctx, &mds)?;
        }
        self.sbox_full(ctx, constants.last().unwrap())?;
        self.apply_mds(ctx, &pre_sparse_mds)?;

        // Partial rounds
        let constants = self.constants_partial();
        for (constant, sparse_mds) in constants.iter().zip(sparse_matrices.iter()) {
            self.sbox_part(ctx, *constant)?;
            self.apply_sparse_mds(ctx, sparse_mds)?;
        }

        // Second half of the full rounds
        let constants = self.constants_end();
        for constants in constants.iter() {
            self.sbox_full(ctx, constants)?;
            self.apply_mds(ctx, &mds)?;
        }
        self.sbox_full(ctx, &[Goldilocks::zero(); T])?;
        self.apply_mds(ctx, &mds)?;

        Ok(())
    }

    fn duplexing(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        input: &[AssignedFieldValue<F>],
    ) -> Result<(), Error> {
        for (word, input) in self.state.0.iter_mut().zip(input.iter()) {
            *word = input.clone();
        }
        self.permutation(ctx)?;

        self.output_buffer.clear();
        self.output_buffer.extend_from_slice(&self.state.0[0..RATE]);
        Ok(())
    }

    pub fn hash_n_to_m_no_pad(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        inputs: Vec<AssignedFieldValue<F>>,
        num_outputs: usize,
    ) -> Result<Vec<AssignedFieldValue<F>>, Error> {
        // Flush the input que
        self.absorbing.clear();

        for chunk in inputs.chunks(RATE) {
            for (word, input) in self.state.0.iter_mut().zip(chunk.iter()) {
                *word = input.clone();
            }
            self.permutation(ctx)?;
        }

        let mut outputs = vec![];
        loop {
            for item in self.state.0.iter().take(RATE) {
                outputs.push(item.clone());
                if outputs.len() == num_outputs {
                    return Ok(outputs);
                }
            }
            self.permutation(ctx)?;
        }
    }

    pub fn hash(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        inputs: Vec<AssignedFieldValue<F>>,
        num_outputs: usize,
    ) -> Result<Vec<AssignedFieldValue<F>>, Error> {
        self.hash_n_to_m_no_pad(ctx, inputs, num_outputs)
    }

    pub fn permute(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        input: Vec<AssignedFieldValue<F>>,
        num_output: usize,
    ) -> Result<Vec<AssignedFieldValue<F>>, Error> {
        for (word, input) in self.state.0.iter_mut().zip(input.iter()) {
            *word = input.clone();
        }
        self.permutation(ctx)?;

        let mut outputs = vec![];
        loop {
            for item in self.state.0.iter().take(RATE) {
                outputs.push(item.clone());
                if outputs.len() == num_output {
                    return Ok(outputs);
                }
            }
            self.permutation(ctx)?;
        }
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        arithmetic::Field,
        circuit::{floor_planner::V1, *},
        dev::MockProver,
        halo2curves::bn256::Fr,
        plonk::*,
    };
    use halo2curves::goldilocks::fp::Goldilocks;
    use halo2wrong_maingate::{fe_to_big, MainGate, MainGateInstructions};
    use plonky2::{
        field::{
            goldilocks_field::GoldilocksField,
            types::{Field as Plonky2Field, PrimeField64},
        },
        hash::poseidon::PoseidonHash,
        plonk::config::Hasher,
    };
    use snark_verifier::util::arithmetic::fe_from_big;

    use crate::snark::verifier_circuit::MainGateWithRangeConfig;

    use super::*;

    #[derive(Default)]
    pub struct GoldilocksPoseidonPermutationCircuit {
        pub input: [Goldilocks; STATE_WIDTH],
        pub output: [Goldilocks; 4],
    }

    impl GoldilocksPoseidonPermutationCircuit {
        pub fn new(input: [Goldilocks; STATE_WIDTH]) -> Self {
            let output =
                PoseidonHash::hash_no_pad(&input.map(|v| GoldilocksField::from_canonical_u64(v.0)));
            let output = output.elements.map(|v| Goldilocks(v.to_canonical_u64()));

            Self { input, output }
        }

        pub fn degree_bits(&self) -> u32 {
            if cfg!(feature = "not-constrain-range-check") {
                11
            } else {
                12
            }
        }

        pub fn instance(&self) -> Vec<Vec<Fr>> {
            let first_column = self.output[0..4]
                .iter()
                .map(|v| fe_from_big::<Fr>(fe_to_big::<Goldilocks>(*v)))
                .collect::<Vec<_>>();

            vec![first_column]
        }
    }

    const STATE_WIDTH: usize = 12;

    #[derive(Clone)]
    pub struct GoldilocksPoseidonPermutationConfig {
        pub goldilocks_chip_config: GoldilocksChipConfig<Fr>,
        pub spec: Spec<Goldilocks, 12, 11>,
    }

    impl Circuit<Fr> for GoldilocksPoseidonPermutationCircuit {
        type Config = GoldilocksPoseidonPermutationConfig;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let main_gate_config = MainGateWithRangeConfig::new(meta);
            let goldilocks_chip_config =
                GoldilocksChip::configure(&main_gate_config.main_gate_config);
            let spec = Spec::<Goldilocks, 12, 11>::new(8, 22);

            GoldilocksPoseidonPermutationConfig {
                goldilocks_chip_config,
                spec,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::new(config.goldilocks_chip_config.main_gate_config.clone());
            let goldilocks_chip = GoldilocksChip::new(&config.goldilocks_chip_config);

            let output_assigned = layouter.assign_region(
                || "addition in the Goldilocks field",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);

                    let mut hasher_chip = HasherChip::<Fr, 12, 11, 8>::new(
                        ctx,
                        &config.spec,
                        &config.goldilocks_chip_config,
                    )?;
                    let input_assigned = self
                        .input
                        .iter()
                        .map(|value| goldilocks_chip.assign_value(ctx, Value::known(*value)))
                        .collect::<Result<Vec<_>, Error>>()?;
                    let output_assigned = hasher_chip.hash_n_to_m_no_pad(ctx, input_assigned, 4)?;
                    for (expected_value, actual_assigned) in
                        self.output.iter().zip(output_assigned.iter())
                    {
                        let expected_assigned =
                            goldilocks_chip.assign_constant(ctx, *expected_value)?;
                        main_gate.assert_equal(ctx, actual_assigned, &expected_assigned)?;
                    }

                    Ok(output_assigned)
                },
            )?;

            for (row, v) in output_assigned.iter().enumerate() {
                main_gate.expose_public(
                    layouter.namespace(|| format!("public input {row}")),
                    v.value.clone(),
                    row,
                )?;
            }

            Ok(())
        }
    }

    #[test]
    fn test_goldilocks_permutation_circuit() {
        let mut input = [Goldilocks::zero(); STATE_WIDTH];
        input[0] = Goldilocks::from(1u64);
        input[4] = Goldilocks::from(2u64);
        let circuit = GoldilocksPoseidonPermutationCircuit::new(input);
        let instance = circuit.instance();
        let k = circuit.degree_bits();

        // runs mock prover
        let mock_prover = MockProver::run(k, &circuit, instance).unwrap();
        mock_prover.assert_satisfied();
    }
}
