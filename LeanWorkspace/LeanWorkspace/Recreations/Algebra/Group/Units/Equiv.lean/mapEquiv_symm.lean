import Mathlib

variable {F α M N G : Type*}

variable [Monoid M] [Monoid N]

theorem mapEquiv_symm (h : M ≃* N) : (Units.mapEquiv h).symm = Units.mapEquiv h.symm := rfl

