import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

variable [Module.Finite R L] [Module.Free R L]

variable [Nontrivial R]

theorem nilRank_le_card {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) : LinearMap.nilRank φ ≤ Fintype.card ι := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [← Module.finrank_eq_card_basis b, ← LinearMap.polyCharpoly_natDegree φ (chooseBasis R L),
    Polynomial.coeff_natDegree, (LinearMap.polyCharpoly_monic _ _).leadingCoeff]
  apply one_ne_zero

