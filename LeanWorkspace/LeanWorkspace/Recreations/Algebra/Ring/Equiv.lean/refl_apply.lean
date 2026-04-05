import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem refl_apply (x : R) : RingEquiv.refl R x = x := rfl

