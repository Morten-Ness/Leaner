import Mathlib

variable {R S M M₂ : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem nat_smul_eq_nsmul (h : Module ℕ M) (n : ℕ) (x : M) : h.smul n x = n • x := Nat.cast_smul_eq_nsmul ..

