use std::marker::PhantomData;

use halo2_proofs::{plonk::Error, circuit::Layouter};
use halo2curves::{goldilocks::fp::Goldilocks, FieldExt};
use halo2wrong::RegionCtx;
use halo2wrong_maingate::AssignedCondition;
use itertools::Itertools;
use poseidon::Spec;

use crate::snark::types::assigned::{AssignedMerkleCapValues, AssignedMerkleProofValues, AssignedFieldValue};

use super::{
    goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig},
    hasher_chip::HasherChip,
    vector_chip::VectorChip,
};

pub struct MerkleProofChip<F: FieldExt> {
    goldilocks_chip_config: GoldilocksChipConfig<F>,
    hasher_config: Spec<Goldilocks, 12, 11>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MerkleProofChip<F> {
    pub fn new(
        goldilocks_chip_config: &GoldilocksChipConfig<F>,
        spec: Spec<Goldilocks, 12, 11>,
    ) -> Self {
        Self {
            goldilocks_chip_config: goldilocks_chip_config.clone(),
            hasher_config: spec,
            _marker: PhantomData,
        }
    }

    fn goldilocks_chip(&self) -> GoldilocksChip<F> {
        GoldilocksChip::new(&self.goldilocks_chip_config)
    }

    fn hasher(&self, ctx: &mut RegionCtx<'_, F>) -> Result<HasherChip<F, 12, 11, 8>, Error> {
        HasherChip::new(ctx, &self.hasher_config, &self.goldilocks_chip_config)
    }

    pub fn verify_merkle_proof_to_cap_with_cap_index(
        &self,
        // ctx: &mut RegionCtx<'_, F>,
        mut layouter: impl Layouter<F>,
        leaf_data: &Vec<AssignedFieldValue<F>>,
        leaf_index_bits: &[AssignedCondition<F>],
        cap_index: &AssignedFieldValue<F>,
        merkle_cap: &AssignedMerkleCapValues<F>,
        proof: &AssignedMerkleProofValues<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "verify_merkle_proof_to_cap_with_cap_index",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

        let mut hasher = self.hasher(ctx)?;
        let goldilocks_chip = self.goldilocks_chip();

        let mut state;
        if leaf_data.len() <= 4 {
            state = leaf_data.clone();
        } else {
            state = hasher.hash(ctx, leaf_data.clone(), 4)?;
        }

        for (bit, sibling) in leaf_index_bits.iter().zip(proof.siblings.iter()) {
            let mut hasher = self.hasher(ctx)?;
            let mut inputs = vec![];
            for i in 0..4 {
                let left = goldilocks_chip.select(ctx, &sibling.elements[i], &state[i], bit)?;
                inputs.push(left);
            }

            for i in 0..4 {
                let right = goldilocks_chip.select(ctx, &state[i], &sibling.elements[i], bit)?;
                inputs.push(right);
            }
            state = hasher.permute(ctx, inputs, 4)?;
        }

        for i in 0..4 {
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

        })
    }
}
