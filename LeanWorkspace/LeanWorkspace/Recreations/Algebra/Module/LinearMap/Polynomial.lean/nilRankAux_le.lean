import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

theorem nilRankAux_le [Nontrivial R] (b : Module.Basis ι R L) (b' : Module.Basis ι' R L) :
    LinearMap.nilRankAux φ b ≤ LinearMap.nilRankAux φ b' := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [Ne, (LinearMap.polyCharpoly_coeff_eq_zero_iff_of_basis φ b b' _).not]
  apply LinearMap.polyCharpoly_coeff_nilRankAux_ne_zero

