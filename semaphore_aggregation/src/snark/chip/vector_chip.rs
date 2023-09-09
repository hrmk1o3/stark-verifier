use halo2_proofs::{arithmetic::Field, plonk::Error};
use halo2curves::{goldilocks::fp::Goldilocks, FieldExt};
use halo2wrong::RegionCtx;

use crate::snark::types::assigned::AssignedFieldValue;

use super::goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig};

pub struct VectorChip<F: FieldExt> {
    goldilocks_chip_config: GoldilocksChipConfig<F>,
    vector: Vec<AssignedFieldValue<F>>,
}

impl<F: FieldExt> VectorChip<F> {
    pub fn new(goldilocks_chip_config: &GoldilocksChipConfig<F>, vector: Vec<AssignedFieldValue<F>>) -> Self {
        Self {
            goldilocks_chip_config: goldilocks_chip_config.clone(),
            vector,
        }
    }

    fn goldilocks_chip(&self) -> GoldilocksChip<F> {
        GoldilocksChip::new(&self.goldilocks_chip_config)
    }

    pub fn access(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        index: &AssignedFieldValue<F>,
    ) -> Result<AssignedFieldValue<F>, Error> {
        let goldilocks_chip = self.goldilocks_chip();

        // this value will be used to check whether the index is in the bound
        let mut not_exists = goldilocks_chip.assign_constant(ctx, Goldilocks::one())?;

        let zero = goldilocks_chip.assign_constant(ctx, Goldilocks::zero())?;
        let mut element = goldilocks_chip.assign_constant(ctx, Goldilocks::zero())?;
        for (i, v) in self.vector.iter().enumerate() {
            let assigned_i = goldilocks_chip.assign_constant(ctx, Goldilocks::from(i as u64))?;
            let i_minus_index = goldilocks_chip.sub(ctx, &assigned_i, index)?;
            not_exists = goldilocks_chip.mul(ctx, &not_exists, &i_minus_index)?;

            let is_same_index = goldilocks_chip.is_equal(ctx, &i_minus_index, &zero)?;
            element = goldilocks_chip.select(ctx, v, &element, &is_same_index)?;
        }
        // if this fails, index is out of the bound, and will return error
        goldilocks_chip.assert_zero(ctx, &not_exists)?;
        Ok(element)
    }
}
