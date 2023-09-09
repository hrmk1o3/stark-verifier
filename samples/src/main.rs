use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use semaphore_aggregation::snark::verifier_api::verify_inside_snark;

/// An example of using Plonky2 to prove a statement of the form
/// "I know n * (n + 1) * ... * (n + 99)".
/// When n == 1, this is proving knowledge of 100!.
fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let inner_stark_verifier_config = CircuitConfig::standard_inner_stark_verifier_config();
    let stark_verifier_config = CircuitConfig::standard_stark_verifier_config();

    let (circuit_data, proof_with_pis) = {
        let inner_config = CircuitConfig {
            zero_knowledge: true, // or false
            ..CircuitConfig::standard_recursion_config()
        };
        let mut builder = CircuitBuilder::<F, D>::new(inner_config);

        // The arithmetic circuit.
        let initial = builder.add_virtual_target();
        let mut cur_target = initial;
        for i in 2..101 {
            let i_target = builder.constant(F::from_canonical_u32(i));
            cur_target = builder.mul(cur_target, i_target);
        }

        // Public inputs are the initial value (provided below) and the result (which is generated).
        builder.register_public_input(initial);
        builder.register_public_input(cur_target);

        let circuit_data = builder.build::<C>();
        dbg!(circuit_data.common.degree_bits());

        let mut pw = PartialWitness::new();
        pw.set_target(initial, F::ONE);
        let proof_with_pis = circuit_data.prove(pw)?;

        println!(
            "Factorial starting at {} is {}",
            proof_with_pis.public_inputs[0], proof_with_pis.public_inputs[1]
        );

        circuit_data.verify(proof_with_pis.clone())?;

        (circuit_data, proof_with_pis)
    };

    let mut builder = CircuitBuilder::<F, D>::new(inner_stark_verifier_config);
    let proof_with_pis_t = builder.add_virtual_proof_with_pis(&circuit_data.common);
    let inner_verifier_data_t = builder.constant_verifier_data(&circuit_data.verifier_only);
    builder.verify_proof::<C>(
        &proof_with_pis_t,
        &inner_verifier_data_t,
        &circuit_data.common,
    );
    builder.register_public_inputs(&proof_with_pis_t.public_inputs);
    let circuit_data = builder.build::<C>();
    dbg!(circuit_data.common.degree_bits());

    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&proof_with_pis_t, &proof_with_pis);
    let proof_with_pis = circuit_data.prove(pw)?;

    let mut builder = CircuitBuilder::<F, D>::new(stark_verifier_config);
    let proof_with_pis_t = builder.add_virtual_proof_with_pis(&circuit_data.common);
    let inner_verifier_data_t = builder.constant_verifier_data(&circuit_data.verifier_only);
    builder.verify_proof::<C>(
        &proof_with_pis_t,
        &inner_verifier_data_t,
        &circuit_data.common,
    );
    builder.register_public_inputs(&proof_with_pis_t.public_inputs);
    let circuit_data = builder.build::<C>();
    dbg!(circuit_data.common.degree_bits());

    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&proof_with_pis_t, &proof_with_pis);
    let proof_with_pis = circuit_data.prove(pw)?;

    verify_inside_snark((
        proof_with_pis,
        circuit_data.verifier_only,
        circuit_data.common,
    ));

    Ok(())
}
