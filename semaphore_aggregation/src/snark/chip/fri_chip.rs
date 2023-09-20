use halo2_proofs::circuit::Layouter;
use halo2_proofs::{arithmetic::Field, plonk::Error};
use halo2_proofs::halo2curves::bn256::Fr;
use halo2curves::{goldilocks::fp::Goldilocks, group::ff::PrimeField, FieldExt};
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{power_of_two, Term, AssignedCondition};
use itertools::Itertools;
use plonky2::util::reverse_index_bits_in_place;
use poseidon::Spec;
use poseidon_circuit::poseidon::Pow5Config;

use crate::snark::types::{
    assigned::{
        AssignedExtensionFieldValue, AssignedFriChallenges, AssignedFriInitialTreeProofValues,
        AssignedFriOpenings, AssignedFriProofValues, AssignedFriQueryRoundValues,
        AssignedMerkleCapValues, AssignedFieldValue,
    },
    common_data::{FriParams, FriConfig},
    fri::{FriBatchInfo, FriInstanceInfo},
};

use super::{
    goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig},
    goldilocks_extension_chip::GoldilocksExtensionChip,
    merkle_proof_chip::MerkleProofChip,
    vector_chip::VectorChip,
};

pub struct FriVerifierChip<F: FieldExt> {
    goldilocks_chip_config: GoldilocksChipConfig<F>,
    hasher_config: Pow5Config<F, 3, 2>,
    spec: Spec<Goldilocks, 12, 11>,
    /// Representative `g` of the coset used in FRI, so that LDEs in FRI are done over `gH`.
    offset: AssignedFieldValue<F>,
    /// The degree of the purported codeword, measured in bits.
    fri_params: FriParams,
}

type F = Fr;

impl FriVerifierChip<F> {
    pub fn construct(
        goldilocks_chip_config: &GoldilocksChipConfig<F>,
        hasher_config: &Pow5Config<F, 3, 2>,
        spec: Spec<Goldilocks, 12, 11>,
        offset: &AssignedFieldValue<F>,
        fri_params: FriParams,
    ) -> Self {
        Self {
            goldilocks_chip_config: goldilocks_chip_config.clone(),
            hasher_config: hasher_config.clone(),
            spec,
            offset: offset.clone(),
            fri_params,
        }
    }

    fn goldilocks_chip(&self) -> GoldilocksChip<F> {
        GoldilocksChip::new(&self.goldilocks_chip_config)
    }

    fn goldilocks_extension_chip(&self) -> GoldilocksExtensionChip<F> {
        GoldilocksExtensionChip::new(&self.goldilocks_chip_config)
    }

    fn verify_proof_of_work(&self, ctx: &mut RegionCtx<'_, F>, fri_pow_response: &AssignedFieldValue<F>, config: &FriConfig) -> Result<(), Error> {
        let goldilocks_chip = GoldilocksChip::new(&self.goldilocks_chip_config);
        goldilocks_chip.assert_leading_zeros(
            ctx,
            fri_pow_response,
            config.proof_of_work_bits + (64 - Goldilocks::NUM_BITS) as u32,
        )
    }

    fn compute_reduced_openings(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        fri_alpha: &AssignedExtensionFieldValue<F, 2>,
        fri_openings: &AssignedFriOpenings<F, 2>,
    ) -> Result<Vec<AssignedExtensionFieldValue<F, 2>>, Error> {
        let goldilocks_extension_chip = GoldilocksExtensionChip::new(&self.goldilocks_chip_config);
        fri_openings
            .batches
            .iter()
            .map(|batch| goldilocks_extension_chip.reduce_extension(ctx, fri_alpha, &batch.values))
            .collect()
    }

    fn calculate_cap_index(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x_index_bits: &[AssignedCondition<F>],
    ) -> Result<AssignedFieldValue<F>, Error> {
        let goldilocks_chip = self.goldilocks_chip();
        let terms = &x_index_bits[x_index_bits.len() - self.fri_params.config.cap_height..]
            .iter()
            .enumerate()
            .map(|(i, bit)| Term::Assigned(&bit, power_of_two(i)))
            .collect_vec();
        goldilocks_chip.compose(ctx, terms, Goldilocks::zero()) // XXX: not constrain this summation
    }

    // evaluation proof for initial polynomials at `x`
    fn verify_initial_merkle_proof(
        &self,
        mut layouter: impl Layouter<F>,
        x_index_bits: &[AssignedCondition<F>],
        cap_index: &AssignedFieldValue<F>,
        initial_merkle_caps: &[AssignedMerkleCapValues<F>],
        initial_trees_proof: &AssignedFriInitialTreeProofValues<F>,
    ) -> Result<(), Error> {
        let merkle_proof_chip =
            MerkleProofChip::new(&self.goldilocks_chip_config, self.spec.clone());
        for (_, ((evals, merkle_proof), cap)) in initial_trees_proof
            .evals_proofs
            .iter()
            .zip(initial_merkle_caps)
            .enumerate()
        {
            merkle_proof_chip.verify_merkle_proof_to_cap_with_cap_index(
                layouter.namespace(|| "verify merkle proof to cap"),
                evals,
                x_index_bits,
                &cap_index,
                &cap,
                merkle_proof,
            )?;
        }
        Ok(())
    }

    fn batch_initial_polynomials(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        fri_instance_info: &FriInstanceInfo<F, 2>,
        fri_alpha: &AssignedExtensionFieldValue<F, 2>,
        // `x` is the initially selected point in FRI
        x: &AssignedFieldValue<F>,
        initial_trees_proof: &AssignedFriInitialTreeProofValues<F>,
        reduced_openings: &[AssignedExtensionFieldValue<F, 2>],
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let goldilocks_extension_chip = self.goldilocks_extension_chip();
        let x = goldilocks_extension_chip.convert_to_extension(ctx, &x)?;
        let mut sum = goldilocks_extension_chip.zero_extension(ctx)?;
        for (batch, reduced_openings) in fri_instance_info
            .batches
            .iter()
            .zip(reduced_openings.iter())
        {
            let FriBatchInfo { point, polynomials } = batch;
            let evals = polynomials
                .iter()
                .map(|p| {
                    let poly_blinding = fri_instance_info.oracles[p.oracle_index].blinding;
                    let salted = self.fri_params.hiding && poly_blinding;
                    initial_trees_proof.unsalted_eval(p.oracle_index, p.polynomial_index, salted)
                })
                .collect_vec();
            let reduced_evals = goldilocks_extension_chip
                .reduce_base_field_terms_extension(ctx, fri_alpha, &evals)?;
            let numerator =
                goldilocks_extension_chip.sub_extension(ctx, &reduced_evals, reduced_openings)?;
            let denominator = goldilocks_extension_chip.sub_extension(ctx, &x, point)?;
            sum = goldilocks_extension_chip.shift(ctx, fri_alpha, evals.len(), &sum)?;
            sum =
                goldilocks_extension_chip.div_add_extension(ctx, &numerator, &denominator, &sum)?;
        }
        Ok(sum) // NOTICE: not use pull/436
    }

    /// obtain subgroup element at index `x_index_bits` from the domain
    fn x_from_subgroup(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x_index_bits: &[AssignedCondition<F>],
    ) -> Result<AssignedFieldValue<F>, Error> {
        let goldilocks_chip = self.goldilocks_chip();
        let lde_size = 1 << self.fri_params.lde_bits();

        // `omega` is the root of unity for initial domain in FRI
        // TODO : add function for primitive root of unity in halo2curves
        let omega = Goldilocks::multiplicative_generator().pow(&[
            ((halo2curves::goldilocks::fp::MODULUS - 1) / lde_size).to_le(),
            0,
            0,
            0,
        ]);
        let x = goldilocks_chip.exp_from_bits(ctx, omega, &x_index_bits[..])?;
        Ok(x)
    }

    fn next_eval(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x_index_within_coset_bits: &[AssignedCondition<F>],
        x: &AssignedFieldValue<F>,
        evals: &Vec<AssignedExtensionFieldValue<F, 2>>,
        arity_bits: usize,
        beta: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let goldilocks_chip = self.goldilocks_chip();
        let goldilocks_extension_chip = self.goldilocks_extension_chip();
        // computes `P'(x^arity)` where `arity = 1 << arity_bits` from `P(x*g^i), (i = 0, ..., arity)` where
        // g is `arity`-th primitive root of unity. P' is FRI folded polynomial.
        let arity = 1 << arity_bits;
        let g = Goldilocks::multiplicative_generator().pow(&[
            ((halo2curves::goldilocks::fp::MODULUS - 1) / arity as u64).to_le(),
            0,
            0,
            0,
        ]);
        let g_inv = g.invert().unwrap();
        let g = goldilocks_chip.assign_constant(ctx, g)?;

        // The evaluation vector needs to be reordered first.
        let mut evals = evals.to_vec();
        reverse_index_bits_in_place(&mut evals);

        let start = goldilocks_chip.exp_from_bits(
            ctx,
            g_inv,
            &x_index_within_coset_bits
                .iter()
                .rev()
                .cloned()
                .collect_vec()[..],
        )?;
        let coset_start = goldilocks_chip.mul(ctx, &start, x)?;

        // The answer is gotten by interpolating {(x*g^i, P(x*g^i))} and evaluating at beta.
        let mut g_power = goldilocks_chip.assign_constant(ctx, Goldilocks::one())?;
        let mut points = vec![];
        for (_, eval) in evals.iter().enumerate() {
            let x = goldilocks_chip.mul(ctx, &coset_start, &g_power)?;
            let x = goldilocks_extension_chip.convert_to_extension(ctx, &x)?;
            g_power = goldilocks_chip.mul(ctx, &g_power, &g)?;
            points.push((x, eval.clone()));
        }
        // Only 2-arity interpolation is supported.
        assert_eq!(evals.len(), 2);
        // a0 -> a1
        // b0 -> b1
        // x  -> a1 + (x-a0)*(b1-a1)/(b0-a0)
        let (a0, a1) = &points[0];
        let (b0, b1) = &points[1];

        // a1 + (x - a0) * (b1 - a1) / (b0 - a0)
        let x_minus_a0 = goldilocks_extension_chip.sub_extension(ctx, beta, a0)?;
        let b1_minus_a1 = goldilocks_extension_chip.sub_extension(ctx, b1, a1)?;
        let numerator = goldilocks_extension_chip.mul_extension(ctx, &x_minus_a0, &b1_minus_a1)?;
        let denominator = goldilocks_extension_chip.sub_extension(ctx, b0, a0)?;
        let result =
            goldilocks_extension_chip.div_add_extension(ctx, &numerator, &denominator, a1)?;
        Ok(result)
    }

    fn check_consistency(
        &self,
        mut layouter: impl Layouter<F>,
        initial_merkle_caps: &[AssignedMerkleCapValues<F>],
        fri_instance_info: &FriInstanceInfo<F, 2>,
        fri_alpha: &AssignedExtensionFieldValue<F, 2>,
        fri_betas: &[AssignedExtensionFieldValue<F, 2>],
        fri_proof: &AssignedFriProofValues<F, 2>,
        x_index: &AssignedFieldValue<F>,
        round_proof: &AssignedFriQueryRoundValues<F, 2>,
        reduced_openings: &[AssignedExtensionFieldValue<F, 2>],
    ) -> Result<(), Error> {
        let goldilocks_chip = self.goldilocks_chip();
        let goldilocks_extension_chip = self.goldilocks_extension_chip();
        let lde_bits = self.fri_params.lde_bits();

        let (mut x_index_bits, cap_index) = layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                // `x_index` is the index of point selected from initial domain
                let x_index_bits = goldilocks_chip
                    .to_bits(ctx, x_index, F::NUM_BITS as usize)?
                    .iter()
                    .take(lde_bits)
                    .cloned()
                    .collect_vec();

                let cap_index = self.calculate_cap_index(ctx, &x_index_bits[..])?;

                Ok((x_index_bits, cap_index))
            }
        )?;

        // start verify_initial_merkle_proof

        // verify evaluation proofs for initial polynomials at `x_index` point
        self.verify_initial_merkle_proof(
            layouter.namespace(|| "verify initial merkle proof"),
            &x_index_bits,
            &cap_index,
            initial_merkle_caps,
            &round_proof.initial_trees_proof,
        )?;

        let (mut x_from_subgroup, mut prev_eval) = layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                let x_from_subgroup =
                    self.x_from_subgroup(ctx, &x_index_bits.iter().rev().cloned().collect_vec())?;
                let x_from_subgroup = goldilocks_chip.mul(ctx, &self.offset, &x_from_subgroup)?; // self.offset = coset_shift // OK

                let prev_eval = self.batch_initial_polynomials(
                    ctx,
                    fri_instance_info,
                    fri_alpha,
                    &x_from_subgroup,
                    &round_proof.initial_trees_proof,
                    reduced_openings,
                )?;

                Ok((x_from_subgroup, prev_eval))
            }
        )?;

        let merkle_proof_chip =
            MerkleProofChip::new(&self.goldilocks_chip_config, self.spec.clone());
        for (i, &arity_bits) in self.fri_params.reduction_arity_bits.iter().enumerate() {
            let evals = &round_proof.steps[i].evals;

            // Split x_index into the index of the coset x is in, and the index of x within that coset.
            let coset_index_bits = x_index_bits[arity_bits..].to_vec();
            let x_index_within_coset_bits = &x_index_bits[..arity_bits];

            layouter.assign_region(
                || "Verify proof",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0); 

                    let x_index_within_coset =
                        goldilocks_chip.from_bits(ctx, &x_index_within_coset_bits.to_vec())?; // XXX: not constrain this summation

                    // check the consistency of `prev_eval` and `next_eval`
                    for i in 0..2 {
                        let vector_chip = VectorChip::new(
                            &self.goldilocks_chip_config,
                            evals.iter().map(|eval| eval.0[i].clone()).collect_vec(),
                        );
                        let next_eval_i = vector_chip.access(ctx, &x_index_within_coset)?;
                        goldilocks_chip.assert_equal(ctx, &prev_eval.0[i], &next_eval_i)?;
                    } // OK, random_access_extension

                    prev_eval = self.next_eval(
                        ctx,
                        x_index_within_coset_bits,
                        &x_from_subgroup,
                        evals,
                        arity_bits,
                        &fri_betas[i],
                    )?;

                    Ok(())
                }
            )?;

            merkle_proof_chip.verify_merkle_proof_to_cap_with_cap_index(
                layouter.namespace(|| "verify merkle proof to cap"),
                &evals.iter().flat_map(|eval| eval.0.clone()).collect::<Vec<_>>(),
                &coset_index_bits,
                &cap_index,
                &fri_proof.commit_phase_merkle_cap_values[i],
                &round_proof.steps[i].merkle_proof,
            )?;
        
            layouter.assign_region(
                || "Verify proof",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);

                    // Update the point x to x^arity.
                    x_from_subgroup = goldilocks_chip.exp_power_of_2(ctx, &x_from_subgroup, arity_bits)?;

                    x_index_bits = coset_index_bits.clone();

                    Ok(())
                }
            )?;
        }

        layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                // Final check of FRI. After all the reductions, we check that the final polynomial is equal
                // to the one sent by the prover.
                let final_poly_coeffs = &fri_proof.final_poly.0;
                let final_poly_eval = goldilocks_extension_chip.reduce_extension_field_terms_base(
                    ctx,
                    &x_from_subgroup,
                    final_poly_coeffs,
                )?;
                goldilocks_extension_chip.assert_equal_extension(ctx, &prev_eval, &final_poly_eval)?;

                Ok(())
            }
        )?;

        Ok(())
    }

    pub fn verify_fri_proof(
        &self,
        mut layouter: impl Layouter<F>,
        initial_merkle_caps: &[AssignedMerkleCapValues<F>],
        fri_challenges: &AssignedFriChallenges<F, 2>,
        fri_openings: &AssignedFriOpenings<F, 2>,
        fri_proof: &AssignedFriProofValues<F, 2>,
        fri_instance_info: &FriInstanceInfo<F, 2>,
    ) -> Result<(), Error> {
        // if let Some(max_arity_bits) = params.max_arity_bits() {
        //     self.check_recursion_config(max_arity_bits);
        // }

        // debug_assert_eq!(
        //     params.final_poly_len(),
        //     proof.final_poly.len(),
        //     "Final polynomial has wrong degree."
        // );

        let reduced_openings = layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                self.verify_proof_of_work(ctx, &fri_challenges.fri_pow_response, &self.fri_params.config)?;

                // // Check that parameters are coherent.
                // debug_assert_eq!(
                //     params.config.num_query_rounds,
                //     proof.query_round_proofs.len(),
                //     "Number of query rounds does not match config."
                // );

                // this value is the same across all queries
                let reduced_openings =
                    self.compute_reduced_openings(ctx, &fri_challenges.fri_alpha, fri_openings)?; // OK: from_os_and_alpha

                Ok(reduced_openings)
            }
        )?;

        for (i, round_proof) in fri_proof.query_round_proofs.iter().enumerate() {
            self.check_consistency(
                layouter.namespace(|| "check consistency"),
                initial_merkle_caps,
                fri_instance_info,
                &fri_challenges.fri_alpha,
                &fri_challenges.fri_betas,
                fri_proof,
                &fri_challenges.fri_query_indices[i],
                round_proof,
                &reduced_openings,
            )?;
        }

        Ok(())
    }
}
