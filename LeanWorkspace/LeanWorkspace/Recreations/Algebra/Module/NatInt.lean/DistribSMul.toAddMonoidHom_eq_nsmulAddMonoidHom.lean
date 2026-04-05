import Mathlib

variable {R S M M₂ : Type*}

variable [AddCommMonoid M]

theorem DistribSMul.toAddMonoidHom_eq_nsmulAddMonoidHom :
    toAddMonoidHom M = nsmulAddMonoidHom := rfl

