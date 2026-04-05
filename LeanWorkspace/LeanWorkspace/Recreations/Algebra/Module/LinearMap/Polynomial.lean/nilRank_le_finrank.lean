import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

variable [Module.Finite R L] [Module.Free R L]

variable [Nontrivial R]

theorem nilRank_le_finrank : LinearMap.nilRank φ ≤ finrank R M := by
  simpa only [finrank_eq_card_chooseBasisIndex R M] using LinearMap.nilRank_le_card φ (chooseBasis R M)

