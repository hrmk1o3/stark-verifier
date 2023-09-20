use std::marker::PhantomData;

use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::{circuit::Layouter, plonk::Error};
use halo2curves::FieldExt;
use halo2wrong::RegionCtx;
use halo2wrong_maingate::AssignedCondition;
use itertools::Itertools;
use poseidon_circuit::poseidon::{primitives::P128Pow5T3, Pow5Chip, Pow5Config};

use crate::snark::types::assigned::{
    AssignedFieldValue, AssignedMerkleCapValues, AssignedMerkleProofValues,
};

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
        let sponge_chip =
            TranscriptChip::new(layouter, &self.hasher_config, &self.goldilocks_chip_config)?;

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
                        let left =
                            goldilocks_chip.select(ctx, &sibling.elements[i], &state[i], bit)?;
                        inputs.push(left);
                    }

                    for i in 0..HASH_OUT_SIZE {
                        let right =
                            goldilocks_chip.select(ctx, &state[i], &sibling.elements[i], bit)?;
                        inputs.push(right);
                    }

                    Ok(inputs)
                },
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
            },
        )?;

        Ok(())
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
        hash::{
            hash_types::HashOut,
            hashing::{compress, hash_n_to_m_no_pad, PlonkyPermutation},
            poseidon::PoseidonHash,
        },
    };
    use poseidon_circuit::poseidon::primitives::P128Pow5T3;
    use snark_verifier::util::arithmetic::fe_from_big;

    use crate::snark::{
        chip::bn254_hasher_chip::{AssignedState, HasherChip},
        config::PoseidonBN128Permutation,
        verifier_circuit::MainGateWithRangeConfig, types::assigned::AssignedHashValues,
    };

    use super::*;

    pub struct Bn254MerkleProofCircuit<const LEAF_SIZE: usize, const TREE_HEIGHT: usize> {
        pub leaf: [Goldilocks; LEAF_SIZE],
        pub index: Goldilocks,
        pub siblings: [[Goldilocks; 4]; TREE_HEIGHT],
        pub root: [Goldilocks; 4],
    }

    impl<const LEAF_SIZE: usize, const TREE_HEIGHT: usize> Default
        for Bn254MerkleProofCircuit<LEAF_SIZE, TREE_HEIGHT>
    {
        fn default() -> Self {
            Self {
                leaf: [Goldilocks::zero(); LEAF_SIZE],
                index: Goldilocks::zero(),
                siblings: [[Goldilocks::zero(); 4]; TREE_HEIGHT],
                root: [Goldilocks::zero(); 4],
            }
        }
    }

    impl<const LEAF_SIZE: usize, const TREE_HEIGHT: usize>
        Bn254MerkleProofCircuit<LEAF_SIZE, TREE_HEIGHT>
    {
        pub fn new(
            leaf: Vec<Goldilocks>,
            index: Goldilocks,
            siblings: Vec<[Goldilocks; 4]>,
        ) -> Self {
            assert_eq!(leaf.len(), LEAF_SIZE);
            assert_eq!(siblings.len(), TREE_HEIGHT);
            let leaf_gl = leaf
                .iter()
                .map(|v| GoldilocksField::from_canonical_u64(v.0))
                .collect::<Vec<_>>();
            let mut node_hash: [GoldilocksField; 4] = hash_n_to_m_no_pad::<
                GoldilocksField,
                PoseidonBN128Permutation<GoldilocksField>,
            >(&leaf_gl, 4)
            .try_into()
            .unwrap();
            let mut index_u64 = GoldilocksField::from_canonical_u64(index.0).to_canonical_u64();
            for sibling in siblings.iter() {
                let sibling_gl = sibling.map(|v| GoldilocksField::from_canonical_u64(v.0));
                let index_bit = index_u64 & 1;
                index_u64 >>= 1;
                let (left, right) = if index_bit == 0 {
                    (
                        HashOut {
                            elements: node_hash,
                        },
                        HashOut {
                            elements: sibling_gl,
                        },
                    )
                } else {
                    (
                        HashOut {
                            elements: sibling_gl,
                        },
                        HashOut {
                            elements: node_hash,
                        },
                    )
                };

                node_hash = compress::<GoldilocksField, PoseidonBN128Permutation<GoldilocksField>>(
                    left, right,
                )
                .elements;
            }

            let root = node_hash
                .iter()
                .map(|v| Goldilocks(v.to_canonical_u64()))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

            Self {
                leaf: leaf.try_into().unwrap(),
                index,
                siblings: siblings.try_into().unwrap(),
                root,
            }
        }

        pub fn degree_bits(&self) -> u32 {
            if cfg!(feature = "not-constrain-range-check") {
                7
            } else {
                8
            }
        }

        pub fn instance(&self) -> Vec<Vec<Fr>> {
            let first_column = self
                .root
                .map(|v| fe_from_big::<Fr>(fe_to_big::<Goldilocks>(v)))
                .to_vec();

            vec![first_column]
        }
    }

    #[derive(Clone)]
    pub struct Bn254MerkleProofConfig {
        pub goldilocks_chip_config: GoldilocksChipConfig<Fr>,
        pub hasher_config: Pow5Config<Fr, 3, 2>,
    }

    impl<const LEAF_SIZE: usize, const TREE_HEIGHT: usize> Circuit<Fr>
        for Bn254MerkleProofCircuit<LEAF_SIZE, TREE_HEIGHT>
    {
        type Config = Bn254MerkleProofConfig;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let main_gate_config = MainGateWithRangeConfig::new(meta);
            let goldilocks_chip_config =
                GoldilocksChip::configure(&main_gate_config.main_gate_config);
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

            Bn254MerkleProofConfig {
                goldilocks_chip_config,
                hasher_config,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::new(config.goldilocks_chip_config.main_gate_config.clone());
            let goldilocks_chip = GoldilocksChip::new(&config.goldilocks_chip_config);
            let mut sponge_chip = TranscriptChip::new(
                &mut layouter,
                &config.hasher_config,
                &config.goldilocks_chip_config,
            )?;

            let input_assigned = layouter.assign_region(
                || "addition in the Goldilocks field",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);

                    self.leaf
                        .iter()
                        .map(|value| goldilocks_chip.assign_value(ctx, Value::known(*value)))
                        .collect::<Result<Vec<_>, Error>>()
                },
            )?;

            let index_bits = layouter.assign_region(
                || "addition in the Goldilocks field",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);

                    let index = goldilocks_chip.assign_value(ctx, Value::known(self.index))?;

                    goldilocks_chip.to_bits(ctx, &index, TREE_HEIGHT)
                },
            )?;

            let mut node_hash = AssignedHashValues {
                elements: sponge_chip
                    .hash_n_to_m_no_pad(&mut layouter, input_assigned, 4)?
                    .try_into()
                    .unwrap(),
            };
            for (b, sibling) in index_bits.iter().zip(self.siblings.iter()) {
                let sibling_assigned = layouter.assign_region(
                    || "addition in the Goldilocks field",
                    |region| {
                        let ctx = &mut RegionCtx::new(region, 0);

                        sibling
                            .iter()
                            .map(|value| goldilocks_chip.assign_value(ctx, Value::known(*value)))
                            .collect::<Result<Vec<_>, Error>>()
                    },
                )?;

                node_hash = sponge_chip.permute_swapped(
                    &mut layouter,
                    node_hash,
                    AssignedHashValues {
                        elements: sibling_assigned.try_into().unwrap()
                    },
                    b,
                )?;
            }

            let output_assigned = node_hash;

            layouter.assign_region(
                || "addition in the Goldilocks field",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);

                    for (expected_value, actual_assigned) in
                        self.root.iter().zip(output_assigned.elements.iter())
                    {
                        let expected_assigned =
                            goldilocks_chip.assign_constant(ctx, *expected_value)?;
                        main_gate.assert_equal(ctx, actual_assigned, &expected_assigned)?;
                    }

                    Ok(())
                },
            )?;

            for (row, v) in output_assigned.elements.iter().enumerate() {
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
    fn test_bn254_merkle_proof_circuit() {
        let mut leaf = vec![Goldilocks::zero(); 8];
        leaf[0] = Goldilocks::from(1u64);
        leaf[4] = Goldilocks::from(2u64);
        let index = Goldilocks::zero();
        let sibling0 = [Goldilocks::from(3u64), Goldilocks::from(4u64), Goldilocks::from(5u64), Goldilocks::from(6u64)];
        let siblings = vec![sibling0];
        let circuit: Bn254MerkleProofCircuit<8, 1> =
            Bn254MerkleProofCircuit::new(leaf, index, siblings);
        let instance = circuit.instance();
        let k = circuit.degree_bits();

        // runs mock prover
        let mock_prover = MockProver::run(k, &circuit, instance).unwrap();
        mock_prover.assert_satisfied();
    }
}
