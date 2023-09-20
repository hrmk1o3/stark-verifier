use crate::snark::{
    chip::bn254_hasher_chip::HasherChip,
    types::assigned::{
        AssignedExtensionFieldValue, AssignedFieldValue, AssignedHashValues,
        AssignedMerkleCapValues,
    },
};
use halo2_proofs::circuit::Layouter;
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::plonk::Error;
use halo2wrong::RegionCtx;
use poseidon::State;
use poseidon_circuit::poseidon::primitives::P128Pow5T3;
use poseidon_circuit::poseidon::Pow5Config;
// use poseidon_circuit::poseidon::primitives::P128Pow5T3Constants;

use super::{bn254_hasher_chip::AssignedState, goldilocks_chip::GoldilocksChipConfig};

type F = Fr;
const T: usize = 3;
const RATE: usize = 2;
const STATE_WIDTH: usize = 12;

// NOTE: implement Challenger
pub struct TranscriptChip {
    hasher_chip: HasherChip<F, P128Pow5T3<F>, T, RATE>,
    state: AssignedState<F, STATE_WIDTH>,
    absorbing: Vec<AssignedFieldValue<F>>,
    output_buffer: Vec<AssignedFieldValue<F>>,
}

impl TranscriptChip {
    /// Constructs the transcript chip
    pub fn new(
        // ctx: &mut RegionCtx<'_, F>,
        layouter: &mut impl Layouter<F>,
        // spec: &Spec<Goldilocks, T, T_MINUS_ONE>,
        hasher_config: &Pow5Config<F, T, RATE>,
        goldilocks_chip_config: &GoldilocksChipConfig<F>,
    ) -> Result<Self, Error> {
        let hasher_chip = HasherChip::<F, P128Pow5T3<F>, T, RATE>::new(
            // ctx,
            hasher_config,
            goldilocks_chip_config,
        )?;
        let goldilocks_chip = hasher_chip.goldilocks_chip();

        let initial_state = layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                State::<_, T>::default()
                    .words()
                    .iter()
                    .map(|word| goldilocks_chip.assign_constant(ctx, *word))
                    .collect::<Result<Vec<_>, Error>>()
            },
        )?;

        Ok(Self {
            hasher_chip,
            state: AssignedState(initial_state.try_into().unwrap()),
            absorbing: vec![],
            output_buffer: vec![],
        })
    }

    /// Appends field elements to the absorbation line. It won't perform
    /// permutation here
    pub fn update(
        &mut self,
        // ctx: &mut RegionCtx<'_, F>,
        element: &AssignedFieldValue<F>,
    ) -> Result<(), Error> {
        self.output_buffer.clear();
        self.absorbing.push(element.clone());
        Ok(())
    }

    fn absorb_buffered_inputs(&mut self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        if self.absorbing.is_empty() {
            return Ok(());
        }
        let buffered_inputs = self.absorbing.clone();
        for input_chunk in buffered_inputs.chunks(RATE) {
            self.duplexing(layouter, input_chunk)?;
        }
        self.absorbing.clear();
        Ok(())
    }

    pub fn squeeze(
        &mut self,
        layouter: &mut impl Layouter<F>,
        num_outputs: usize,
    ) -> Result<Vec<AssignedFieldValue<F>>, Error> {
        let mut output = vec![];
        for _i in 0..num_outputs {
            self.absorb_buffered_inputs(layouter)?;

            if self.output_buffer.is_empty() {
                self.state = self.hasher_chip.permutation(layouter, self.state.clone())?;
                self.output_buffer = self.state.0[0..RATE].to_vec();
            }
            output.push(self.output_buffer.pop().unwrap())
        }
        Ok(output)
    }

    fn duplexing(
        &mut self,
        layouter: &mut impl Layouter<F>,
        input: &[AssignedFieldValue<F>],
    ) -> Result<(), Error> {
        for (word, input) in self.state.0.iter_mut().zip(input.iter()) {
            *word = input.clone();
        }
        self.state = self.hasher_chip.permutation(layouter, self.state.clone())?;

        self.output_buffer.clear();
        self.output_buffer.extend_from_slice(&self.state.0[0..RATE]);
        Ok(())
    }

    pub fn hash(
        &mut self,
        layouter: &mut impl Layouter<F>,
        inputs: Vec<AssignedFieldValue<F>>,
        num_outputs: usize,
    ) -> Result<Vec<AssignedFieldValue<F>>, Error> {
        // Flush the input que
        self.absorbing.clear();

        for chunk in inputs.chunks(RATE) {
            for (word, input) in self.state.0.iter_mut().zip(chunk.iter()) {
                *word = input.clone();
            }
            self.state = self.hasher_chip.permutation(layouter, self.state.clone())?;
        }

        let mut outputs = vec![];
        loop {
            for item in self.state.0.iter().take(RATE) {
                outputs.push(item.clone());
                if outputs.len() == num_outputs {
                    return Ok(outputs);
                }
            }
            self.state = self.hasher_chip.permutation(layouter, self.state.clone())?;
        }
    }

    // pub fn permute(
    //     &mut self,
    //     layouter: &mut impl Layouter<F>,
    //     input: Vec<AssignedFieldValue<F>>,
    //     num_output: usize,
    // ) -> Result<Vec<AssignedFieldValue<F>>, Error> {
    //     for (word, input) in self.state.0.iter_mut().zip(input.iter()) {
    //         *word = input.clone();
    //     }
    //     self.permutation(layouter)?;

    //     let mut outputs = vec![];
    //     loop {
    //         for item in self.state.0.iter().take(RATE) {
    //             outputs.push(item.clone());
    //             if outputs.len() == num_output {
    //                 return Ok(outputs);
    //             }
    //         }
    //         self.permutation(layouter)?;
    //     }
    // }
}

impl TranscriptChip {
    /// Write scalar to the transcript
    pub fn write_scalar(
        &mut self,
        // ctx: &mut RegionCtx<'_, N>,
        scalar: &AssignedFieldValue<F>,
    ) -> Result<(), Error> {
        self.update(scalar)
    }

    pub fn write_extension<const D: usize>(
        &mut self,
        // ctx: &mut RegionCtx<'_, N>,
        extension: &AssignedExtensionFieldValue<F, D>,
    ) -> Result<(), Error> {
        for scalar in extension.0.iter() {
            self.write_scalar(scalar)?;
        }
        Ok(())
    }

    pub fn write_hash(
        &mut self,
        // ctx: &mut RegionCtx<'_, N>,
        hash: &AssignedHashValues<F>,
    ) -> Result<(), Error> {
        for scalar in hash.elements.iter() {
            self.write_scalar(scalar)?;
        }
        Ok(())
    }

    pub fn write_cap(
        &mut self,
        // ctx: &mut RegionCtx<'_, N>,
        cap: &AssignedMerkleCapValues<F>,
    ) -> Result<(), Error> {
        for hash in cap.0.iter() {
            self.write_hash(&hash)?;
        }
        Ok(())
    }
}
