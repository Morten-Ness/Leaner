import Mathlib

variable {R : Type*}

theorem unop_natCast [NatCast R] (n : ℕ) : unop (n : Rᵐᵒᵖ) = n := rfl

