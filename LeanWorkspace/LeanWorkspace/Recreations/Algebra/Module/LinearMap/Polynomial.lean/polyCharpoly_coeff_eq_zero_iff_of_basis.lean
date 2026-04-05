import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

theorem polyCharpoly_coeff_eq_zero_iff_of_basis (b : Module.Basis ι R L) (b' : Module.Basis ι' R L) (k : ℕ) :
    (LinearMap.polyCharpoly φ b).coeff k = 0 ↔ (LinearMap.polyCharpoly φ b').coeff k = 0 := by
  constructor <;> apply LinearMap.polyCharpoly_coeff_eq_zero_of_basis

