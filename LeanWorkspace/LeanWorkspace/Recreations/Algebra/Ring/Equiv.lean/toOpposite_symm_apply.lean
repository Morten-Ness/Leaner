import Mathlib

variable {F α β R S S' : Type*}

variable (R) [NonUnitalCommSemiring R]

theorem toOpposite_symm_apply (r : Rᵐᵒᵖ) : (RingEquiv.toOpposite R).symm r = unop r := rfl

