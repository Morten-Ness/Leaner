import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

theorem nilRankAux_basis_indep [Nontrivial R] (b : Module.Basis ι R L) (b' : Module.Basis ι' R L) :
    LinearMap.nilRankAux φ b = (LinearMap.polyCharpoly φ b').natTrailingDegree := by
  apply le_antisymm <;> apply LinearMap.nilRankAux_le

