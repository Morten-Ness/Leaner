import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]

variable [SMulCommClass R A A]

theorem symm_mulLeftLinearEquiv_apply (a : Aˣ) (x : A) :
    (a.mulLeftLinearEquiv R A).symm x = a⁻¹ * x := rfl

