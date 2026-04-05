import Mathlib

variable {R A B C : Type*}

variable [AddCommMonoid A]

variable [Semiring R] [Module R A] [AddCommMonoid B] [Module R B]

theorem symm_congrLinearEquiv_apply (f : A ≃ₗ[R] B) (x : WithConv B) :
    (WithConv.congrLinearEquiv f).symm x = toConv (f.symm x.ofConv) := by simp

