import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

theorem polyCharpoly_coeff_nilRankAux_ne_zero [Nontrivial R] :
    (LinearMap.polyCharpoly φ b).coeff (LinearMap.nilRankAux φ b) ≠ 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  apply LinearMap.polyCharpoly_ne_zero

