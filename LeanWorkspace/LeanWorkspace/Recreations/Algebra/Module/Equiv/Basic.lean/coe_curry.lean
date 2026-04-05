import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M]

theorem coe_curry : ⇑(LinearEquiv.curry R M V V₂) = curry := rfl

