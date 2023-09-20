use halo2_proofs::circuit::Value;
use halo2curves::FieldExt;
use halo2wrong_maingate::AssignedValue;

#[derive(Clone)]
pub struct AssignedHashValues<F: FieldExt> {
    pub elements: [AssignedFieldValue<F>; 4],
}

#[derive(Clone)]
pub struct AssignedMerkleCapValues<F: FieldExt>(pub Vec<AssignedHashValues<F>>);

#[derive(Clone, Debug)]
pub struct AssignedFieldValue<F: FieldExt>{
    pub(crate) value: AssignedValue<F>,
    pub(crate) is_asserted: std::cell::Cell<bool>,
}

impl<F: FieldExt> From<AssignedValue<F>> for AssignedFieldValue<F> {
    fn from(value: AssignedValue<F>) -> Self {
        Self { value, is_asserted: std::cell::Cell::new(false) }
    }
}

impl<F: FieldExt> From<AssignedFieldValue<F>> for AssignedValue<F> {
    fn from(value: AssignedFieldValue<F>) -> Self {
        assert!(value.is_asserted());

        value.value
    }
}


impl<F: FieldExt> AssignedFieldValue<F> {
    pub fn asserted(value: AssignedValue<F>) -> Self {
        Self { value, is_asserted: std::cell::Cell::new(true) }
    }

    pub fn is_asserted(&self) -> bool {
        self.is_asserted.get()
    }

    pub fn value(&self) -> Value<&F> {
        assert!(self.is_asserted());

        self.value.value()
    }

    pub fn value_unchecked(&self) -> Value<&F> {
        self.value.value()
    }
}

impl<F: FieldExt> std::ops::Deref for AssignedFieldValue<F> {
    type Target = AssignedValue<F>;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<F: FieldExt> std::ops::DerefMut for AssignedFieldValue<F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<F: FieldExt> AsRef<AssignedValue<F>> for AssignedFieldValue<F> {
    fn as_ref(&self) -> &AssignedValue<F> {
        &self.value
    }
}

impl<F: FieldExt> AsMut<AssignedValue<F>> for AssignedFieldValue<F> {
    fn as_mut(&mut self) -> &mut AssignedValue<F> {
        &mut self.value
    }
}

#[derive(Clone, Debug)]
pub struct AssignedExtensionFieldValue<F: FieldExt, const D: usize>(pub [AssignedFieldValue<F>; D]);

impl<F: FieldExt, const D: usize> From<[AssignedFieldValue<F>; D]> for AssignedExtensionFieldValue<F, D> {
    fn from(value: [AssignedFieldValue<F>; D]) -> Self {
        Self(value)
    }
}

impl<F: FieldExt, const D: usize> std::ops::Deref for AssignedExtensionFieldValue<F, D> {
    type Target = [AssignedFieldValue<F>; D];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub struct AssignedOpeningSetValues<F: FieldExt, const D: usize> {
    pub constants: Vec<AssignedExtensionFieldValue<F, D>>,
    pub plonk_sigmas: Vec<AssignedExtensionFieldValue<F, D>>,
    pub wires: Vec<AssignedExtensionFieldValue<F, D>>,
    pub plonk_zs: Vec<AssignedExtensionFieldValue<F, D>>,
    pub plonk_zs_next: Vec<AssignedExtensionFieldValue<F, D>>,
    pub partial_products: Vec<AssignedExtensionFieldValue<F, D>>,
    pub quotient_polys: Vec<AssignedExtensionFieldValue<F, D>>,
}

impl<F: FieldExt, const D: usize> AssignedOpeningSetValues<F, D> {
    pub(crate) fn to_fri_openings(&self) -> AssignedFriOpenings<F, D> {
        let zeta_batch = AssignedFriOpeningBatch {
            values: [
                self.constants.as_slice(),
                self.plonk_sigmas.as_slice(),
                self.wires.as_slice(),
                self.plonk_zs.as_slice(),
                self.partial_products.as_slice(),
                self.quotient_polys.as_slice(),
            ]
            .concat(),
        };
        let zeta_next_batch = AssignedFriOpeningBatch {
            values: self.plonk_zs_next.clone(),
        };
        AssignedFriOpenings {
            batches: vec![zeta_batch, zeta_next_batch],
        }
    }
}

#[derive(Clone)]
pub struct AssignedMerkleProofValues<F: FieldExt> {
    pub siblings: Vec<AssignedHashValues<F>>,
}

#[derive(Clone)]
pub struct AssignedFriInitialTreeProofValues<F: FieldExt> {
    pub evals_proofs: Vec<(Vec<AssignedFieldValue<F>>, AssignedMerkleProofValues<F>)>,
}

impl<F: FieldExt> AssignedFriInitialTreeProofValues<F> {
    pub(crate) fn unsalted_eval(
        &self,
        oracle_index: usize,
        poly_index: usize,
        salted: bool,
    ) -> AssignedFieldValue<F> {
        self.unsalted_evals(oracle_index, salted)[poly_index].clone()
    }

    fn unsalted_evals(&self, oracle_index: usize, salted: bool) -> &[AssignedFieldValue<F>] {
        let evals = &self.evals_proofs[oracle_index].0;
        let salt_size = if salted { 4 } else { 0 };
        &evals[..evals.len() - salt_size]
    }
}

#[derive(Clone)]
pub struct AssignedFriQueryStepValues<F: FieldExt, const D: usize> {
    pub evals: Vec<AssignedExtensionFieldValue<F, D>>,
    pub merkle_proof: AssignedMerkleProofValues<F>,
}

#[derive(Clone)]
pub struct AssignedFriQueryRoundValues<F: FieldExt, const D: usize> {
    pub initial_trees_proof: AssignedFriInitialTreeProofValues<F>,
    pub steps: Vec<AssignedFriQueryStepValues<F, D>>,
}

#[derive(Clone)]
pub struct AssignedPolynomialCoeffsExtValues<F: FieldExt, const D: usize>(
    pub Vec<AssignedExtensionFieldValue<F, D>>,
);

#[derive(Clone)]
pub struct AssignedFriProofValues<F: FieldExt, const D: usize> {
    pub commit_phase_merkle_cap_values: Vec<AssignedMerkleCapValues<F>>,
    pub query_round_proofs: Vec<AssignedFriQueryRoundValues<F, D>>,
    pub final_poly: AssignedPolynomialCoeffsExtValues<F, D>,
    pub pow_witness: AssignedFieldValue<F>,
}

pub struct AssignedProofValues<F: FieldExt, const D: usize> {
    pub wires_cap: AssignedMerkleCapValues<F>,
    pub plonk_zs_partial_products_cap: AssignedMerkleCapValues<F>,
    pub quotient_polys_cap: AssignedMerkleCapValues<F>,

    pub openings: AssignedOpeningSetValues<F, D>,
    pub opening_proof: AssignedFriProofValues<F, D>,
}

pub struct AssignedProofWithPisValues<F: FieldExt, const D: usize> {
    pub proof: AssignedProofValues<F, D>,
    pub public_inputs: Vec<AssignedFieldValue<F>>,
}

pub struct AssignedVerificationKeyValues<F: FieldExt> {
    pub constants_sigmas_cap: AssignedMerkleCapValues<F>,
    pub circuit_digest: AssignedHashValues<F>,
}

#[derive(Clone)]
pub struct AssignedFriChallenges<F: FieldExt, const D: usize> {
    pub fri_alpha: AssignedExtensionFieldValue<F, D>,
    pub fri_betas: Vec<AssignedExtensionFieldValue<F, D>>,
    pub fri_pow_response: AssignedFieldValue<F>,
    pub fri_query_indices: Vec<AssignedFieldValue<F>>,
}

/// Opened values of each polynomial.
pub struct AssignedFriOpenings<F: FieldExt, const D: usize> {
    pub batches: Vec<AssignedFriOpeningBatch<F, D>>,
}

/// Opened values of each polynomial that's opened at a particular point.
pub struct AssignedFriOpeningBatch<F: FieldExt, const D: usize> {
    pub values: Vec<AssignedExtensionFieldValue<F, D>>,
}

pub struct AssignedProofChallenges<F: FieldExt, const D: usize> {
    pub plonk_betas: Vec<AssignedFieldValue<F>>,
    pub plonk_gammas: Vec<AssignedFieldValue<F>>,
    pub plonk_alphas: Vec<AssignedFieldValue<F>>,
    pub plonk_zeta: AssignedExtensionFieldValue<F, D>,
    pub fri_challenges: AssignedFriChallenges<F, D>,
}
