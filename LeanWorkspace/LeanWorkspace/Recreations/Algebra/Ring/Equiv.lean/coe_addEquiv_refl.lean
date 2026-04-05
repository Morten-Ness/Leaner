import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem coe_addEquiv_refl : (RingEquiv.refl R : R ≃+ R) = AddEquiv.refl R := rfl

