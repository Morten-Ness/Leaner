import Mathlib

variable {R S M M₂ : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

theorem two_smul : (2 : R) • x = x + x := by rw [← one_add_one_eq_two, add_smul, one_smul]

