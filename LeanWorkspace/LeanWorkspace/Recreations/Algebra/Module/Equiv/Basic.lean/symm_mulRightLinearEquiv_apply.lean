import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]

variable [IsScalarTower R A A]

theorem symm_mulRightLinearEquiv_apply (a : Aˣ) (x : A) :
    (a.mulRightLinearEquiv R).symm x = x * a⁻¹ := rfl

