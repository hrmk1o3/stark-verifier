use std::marker::PhantomData;

use halo2_proofs::{plonk::Error, circuit::Layouter};
use halo2_proofs::halo2curves::bn256::Fr;
use halo2curves::FieldExt;
use halo2wrong::RegionCtx;
use halo2wrong_maingate::AssignedCondition;
use itertools::Itertools;
use poseidon_circuit::poseidon::{Pow5Config, Pow5Chip, primitives::P128Pow5T3};

use crate::snark::types::assigned::{AssignedMerkleCapValues, AssignedMerkleProofValues, AssignedFieldValue};

use super::{
    bn254_transcript_chip::TranscriptChip,
    goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig},
    vector_chip::VectorChip,
};

const HASH_OUT_SIZE: usize = 4;

pub struct MerkleProofChip<F: FieldExt> {
    goldilocks_chip_config: GoldilocksChipConfig<F>,
    hasher_config: Pow5Config<F, 3, 2>,
    // spec: Spec<F, 3, 2>,
    _marker: PhantomData<F>,
}

type F = Fr;

impl MerkleProofChip<F> {
    pub fn new(
        goldilocks_chip_config: &GoldilocksChipConfig<F>,
        hasher_config: &Pow5Config<F, 3, 2>,
        // spec: Spec<F, 3, 2>,
    ) -> Self {
        Self {
            goldilocks_chip_config: goldilocks_chip_config.clone(),
            hasher_config: hasher_config.clone(),
            // spec,
            _marker: PhantomData,
        }
    }

    fn goldilocks_chip(&self) -> GoldilocksChip<F> {
        GoldilocksChip::new(&self.goldilocks_chip_config)
    }

    fn sponge_chip(&self, layouter: &mut impl Layouter<F>) -> Result<TranscriptChip, Error> {
        let sponge_chip = TranscriptChip::new(
            layouter,
            &self.hasher_config,
            &self.goldilocks_chip_config,
        )?;

        Ok(sponge_chip)
    }

    pub fn verify_merkle_proof_to_cap_with_cap_index(
        &self,
        mut layouter: impl Layouter<F>,
        leaf_data: &[AssignedFieldValue<F>],
        leaf_index_bits: &[AssignedCondition<F>],
        cap_index: &AssignedFieldValue<F>,
        merkle_cap: &AssignedMerkleCapValues<F>,
        proof: &AssignedMerkleProofValues<F>,
    ) -> Result<(), Error> {
        let goldilocks_chip = self.goldilocks_chip();

        let mut state = if leaf_data.len() <= HASH_OUT_SIZE {
            leaf_data.to_vec()
        } else {
            // let hasher: poseidon_circuit::poseidon::Hash<F,_,P128Pow5T3<F>,3,2> = poseidon_circuit::poseidon::Hash::init(
            //     hasher_chip.clone(),
            //     layouter.namespace(|| "init"),
            //     &[F::from_u128(leaf_data.len() as u128)] // ConstantLength<L>::initial_capacity_elements()
            // ).unwrap();
            // let output = hasher.hash(
            //     layouter.namespace(|| "leaf hash"),
            //     &leaf_data.iter().map(|v| (**v).clone()).collect::<Vec<_>>()
            // ).unwrap().into();
            // state = hasher.hash(ctx, leaf_data.clone(), HASH_OUT_SIZE)?;
            let mut sponge_chip = self.sponge_chip(&mut layouter)?;

            sponge_chip.hash_n_to_m_no_pad(&mut layouter, leaf_data.to_vec(), HASH_OUT_SIZE)?
        };
        debug_assert_eq!(state.len(), HASH_OUT_SIZE);

        for (bit, sibling) in leaf_index_bits.iter().zip(proof.siblings.iter()) {
            let inputs = layouter.assign_region(
                || "Verify proof",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    
                    let mut inputs = vec![];
                    assert_eq!(sibling.elements.len(), HASH_OUT_SIZE);
                    // TODO: implement swap
                    for i in 0..HASH_OUT_SIZE {
                        let left = goldilocks_chip.select(ctx, &sibling.elements[i], &state[i], bit)?;
                        inputs.push(left);
                    }
        
                    for i in 0..HASH_OUT_SIZE {
                        let right = goldilocks_chip.select(ctx, &state[i], &sibling.elements[i], bit)?;
                        inputs.push(right);
                    }

                    Ok(inputs)
                }
            )?;

            let mut sponge_chip = self.sponge_chip(&mut layouter)?;

            state = sponge_chip.hash_n_to_m_no_pad(&mut layouter, inputs, HASH_OUT_SIZE)?;
        }

        layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                for i in 0..HASH_OUT_SIZE {
                    let vector_chip = VectorChip::new(
                        &self.goldilocks_chip_config,
                        merkle_cap
                            .0
                            .iter()
                            .map(|hash| hash.elements[i].clone())
                            .collect_vec(),
                    );
                    let cap_i = vector_chip.access(ctx, &cap_index)?;
                    goldilocks_chip.assert_equal(ctx, &cap_i, &state[i])?;
                }

                Ok(())
            }
        )?;

        Ok(())
    }
}
