use plonky2::hash::poseidon::{HALF_N_FULL_ROUNDS, N_PARTIAL_ROUNDS, SPONGE_WIDTH, SPONGE_RATE};
const T: usize = SPONGE_WIDTH;
const T_MINUS_ONE: usize = SPONGE_WIDTH - 1;
const RATE: usize = SPONGE_RATE;

const R_F: usize = HALF_N_FULL_ROUNDS * 2;
const R_F_HALF: usize = HALF_N_FULL_ROUNDS;
const R_P: usize = N_PARTIAL_ROUNDS;

pub mod chip;
pub mod types;
pub mod utils;
pub mod verifier_api;
pub mod verifier_circuit;
