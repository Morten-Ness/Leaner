import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem coe_mulEquiv_refl : (RingEquiv.refl R : R ≃* R) = MulEquiv.refl R := rfl

