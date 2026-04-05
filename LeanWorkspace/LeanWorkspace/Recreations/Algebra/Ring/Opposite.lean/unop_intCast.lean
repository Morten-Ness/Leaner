import Mathlib

variable {R : Type*}

theorem unop_intCast [IntCast R] (n : ℤ) : unop (n : Rᵐᵒᵖ) = n := rfl

