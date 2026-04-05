import Mathlib

variable {R S M M₂ : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

theorem int_smul_eq_zsmul (h : Module ℤ M) (n : ℤ) (x : M) : h.smul n x = n • x := Int.cast_smul_eq_zsmul ..

