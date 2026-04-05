import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem coe_refl (R : Type*) [Mul R] [Add R] : ⇑(RingEquiv.refl R) = id := rfl

