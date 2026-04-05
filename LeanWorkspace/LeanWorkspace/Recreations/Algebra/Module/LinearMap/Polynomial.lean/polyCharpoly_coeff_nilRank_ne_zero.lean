import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

variable [Module.Finite R L] [Module.Free R L]

variable [Nontrivial R]

theorem polyCharpoly_coeff_nilRank_ne_zero :
    (LinearMap.polyCharpoly φ b).coeff (LinearMap.nilRank φ) ≠ 0 := by
  rw [LinearMap.nilRank_eq_polyCharpoly_natTrailingDegree _ b]
  apply LinearMap.polyCharpoly_coeff_nilRankAux_ne_zero

