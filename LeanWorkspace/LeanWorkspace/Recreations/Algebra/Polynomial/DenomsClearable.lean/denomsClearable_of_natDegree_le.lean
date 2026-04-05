import Mathlib

open scoped Polynomial

variable {R K : Type*} [Semiring R] [CommSemiring K] {i : R →+* K}

variable {a b : R} {bi : K}

theorem denomsClearable_of_natDegree_le (N : ℕ) (a : R) (bu : bi * i b = 1) :
    ∀ f : R[X], f.natDegree ≤ N → DenomsClearable a b N f i := induction_with_natDegree_le _ N (denomsClearable_zero N a bu)
    (fun _ r _ => denomsClearable_C_mul_X_pow a bu r) fun _ _ _ _ df dg => df.add dg

