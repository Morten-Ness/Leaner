import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable (R) [Semiring R] [AddCommGroup M] [Module R M]

theorem neg_apply (x : M) : LinearEquiv.neg R x = -x := by simp

