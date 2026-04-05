import Mathlib

variable {F α β R S S' : Type*}

variable (R) [NonUnitalCommSemiring R]

theorem toOpposite_apply (r : R) : RingEquiv.toOpposite R r = op r := rfl

