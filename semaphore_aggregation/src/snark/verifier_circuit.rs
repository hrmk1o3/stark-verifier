use crate::snark::types::proof::ProofValues;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{floor_planner::V1, *},
    halo2curves::bn256::Fr,
    plonk::*,
};
use halo2curves::goldilocks::fp::Goldilocks;
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{MainGate, MainGateConfig, MainGateInstructions, big_to_fe, fe_to_big};
use itertools::Itertools;
use poseidon::Spec;
use poseidon_circuit::poseidon::{Pow5Chip, Pow5Config};
use std::marker::PhantomData;

use super::{
    chip::{
        goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig},
        plonk::plonk_verifier_chip::PlonkVerifierChip,
    },
    types::{
        assigned::{
            AssignedProofValues, AssignedProofWithPisValues, AssignedVerificationKeyValues,
        },
        common_data::CommonData,
        proof::{FriProofValues, OpeningSetValues},
        verification_key::VerificationKeyValues,
        HashValues, MerkleCapValues,
    },
    R_F, R_P, T, T_MINUS_ONE,
};

#[derive(Clone)]
pub struct MainGateWithRangeConfig<F: FieldExt> {
    pub main_gate_config: MainGateConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MainGateWithRangeConfig<F> {
    pub fn new(meta: &mut ConstraintSystem<F>) -> Self {
        let main_gate_config = MainGate::<F>::configure(meta);
        MainGateWithRangeConfig {
            main_gate_config,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone)]
pub struct Verifier<S: poseidon_circuit::poseidon::primitives::Spec<Fr, WIDTH, RATE>> {
    proof: ProofValues<Fr, 2>,
    instances: Vec<Fr>,
    vk: VerificationKeyValues<Fr>,
    common_data: CommonData<Fr>,
    spec: Spec<Goldilocks, T, T_MINUS_ONE>,
    _spec: PhantomData<S>,
}

impl<S: poseidon_circuit::poseidon::primitives::Spec<Fr, WIDTH, RATE>> Verifier<S> {
    pub fn new(
        proof: ProofValues<Fr, 2>,
        instances: Vec<Fr>,
        vk: VerificationKeyValues<Fr>,
        common_data: CommonData<Fr>,
        spec: Spec<Goldilocks, T, T_MINUS_ONE>,
    ) -> Self {
        Self {
            proof,
            instances,
            vk,
            common_data,
            spec,
            _spec: std::marker::PhantomData
        }
    }

    fn assign_proof_with_pis(
        &self,
        config: &GoldilocksChipConfig<Fr>,
        mut layouter: impl Layouter<Fr>,
        proof: &ProofValues<Fr, 2>,
        instances: &Vec<Fr>,
    ) -> Result<AssignedProofWithPisValues<Fr, 2>, Error> {
        let public_inputs = layouter.assign_region(
            || "Assign Plonky2 public inputs",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let goldilocks_chip = GoldilocksChip::new(config);
                let max = fe_to_big(-Goldilocks::from(1));

                let public_inputs = instances
                    .iter()
                    .map(|instance| goldilocks_chip.assign_value(ctx, {
                        assert!(fe_to_big(*instance) <= max);

                        Value::known(big_to_fe(fe_to_big(*instance)))
                    }))
                    .collect::<Result<Vec<_>, Error>>()?;

                Ok(public_inputs)
            },
        )?;

        let wires_cap =
            MerkleCapValues::assign(config, layouter.namespace(|| ""), &proof.wires_cap)?;
        let plonk_zs_partial_products_cap = MerkleCapValues::assign(
            config,
            layouter.namespace(|| ""),
            &proof.plonk_zs_partial_products_cap,
        )?;
        let quotient_polys_cap =
            MerkleCapValues::assign(config, layouter.namespace(|| ""), &proof.quotient_polys_cap)?;
        let openings =
            OpeningSetValues::assign(config, layouter.namespace(|| ""), &proof.openings)?;
        let opening_proof =
            FriProofValues::assign(config, layouter.namespace(|| ""), &proof.opening_proof)?;
        Ok(AssignedProofWithPisValues {
            proof: AssignedProofValues {
                wires_cap,
                plonk_zs_partial_products_cap,
                quotient_polys_cap,
                openings,
                opening_proof,
            },
            public_inputs,
        })
    }

    pub fn assign_verification_key(
        &self,
        config: &GoldilocksChipConfig<Fr>,
        mut layouter: impl Layouter<Fr>,
        vk: &VerificationKeyValues<Fr>,
    ) -> Result<AssignedVerificationKeyValues<Fr>, Error> {
        Ok(AssignedVerificationKeyValues {
            constants_sigmas_cap: MerkleCapValues::assign(
                config,
                layouter.namespace(|| ""),
                &vk.constants_sigmas_cap,
            )?,
            circuit_digest: HashValues::assign(
                config,
                layouter.namespace(|| ""),
                &vk.circuit_digest,
            )?,
        })
    }
}

const WIDTH: usize = 3;
const RATE: usize = 2;

#[derive(Clone)]
pub struct VerifierConfig {
    pub hasher_config: Pow5Config<Fr, WIDTH, RATE>,
    pub main_gate_config: MainGateWithRangeConfig<Fr>,
}

impl<S: poseidon_circuit::poseidon::primitives::Spec<Fr, WIDTH, RATE>> Circuit<Fr> for Verifier<S> {
    type Config = VerifierConfig;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self {
            proof: self.proof.clone(),
            instances: self.instances.clone(),
            vk: self.vk.clone(),
            common_data: self.common_data.clone(),
            spec: Spec::new(R_F, R_P),
            _spec: std::marker::PhantomData
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let state = (0..WIDTH).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let hasher_config = {
            let partial_sbox = meta.advice_column();

            let rc_a = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();
            let rc_b = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();

            meta.enable_constant(rc_b[0]);

            Pow5Chip::configure::<S>(
                meta,
                state.try_into().unwrap(),
                partial_sbox,
                rc_a.try_into().unwrap(),
                rc_b.try_into().unwrap(),
            )
        };

        let main_gate_config = MainGateWithRangeConfig::new(meta);

        VerifierConfig {
            hasher_config, main_gate_config
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let main_gate = MainGate::new(config.main_gate_config.main_gate_config.clone());
        let goldilocks_chip_config = GoldilocksChip::configure(&config.main_gate_config.main_gate_config);
        let assigned_proof_with_pis = self.assign_proof_with_pis(
            &goldilocks_chip_config,
            layouter.namespace(|| "Assign proof and public inputs"),
            &self.proof,
            &self.instances,
        )?;
        let assigned_vk = self.assign_verification_key(
            &goldilocks_chip_config,
            layouter.namespace(|| "Assign verification key"),
            &self.vk,
        )?;
        let plonk_verifier_chip = PlonkVerifierChip::construct(&goldilocks_chip_config);

        let public_inputs_hash = layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                
                plonk_verifier_chip.get_public_inputs_hash(
                    ctx,
                    &assigned_proof_with_pis.public_inputs,
                    &self.spec,
                )
            },
        )?;

        let challenges = plonk_verifier_chip.get_challenges(
            &mut layouter,
            &public_inputs_hash,
            &assigned_vk.circuit_digest,
            &self.common_data,
            &assigned_proof_with_pis.proof,
            self.common_data.config.num_challenges,
            &self.spec,
        )?;

        plonk_verifier_chip.verify_proof_with_challenges(
            layouter.namespace(|| "verify proof with challenges"),
            &assigned_proof_with_pis.proof,
            &public_inputs_hash,
            &challenges,
            &assigned_vk,
            &self.common_data,
            &config.hasher_config,
            &self.spec,
        )?;

        for (row, public_input) in
            (0..self.instances.len()).zip_eq(assigned_proof_with_pis.public_inputs)
        {
            main_gate.expose_public(layouter.namespace(|| ""), (*public_input).clone(), row)?;
        }

        Ok(())
    }
}
