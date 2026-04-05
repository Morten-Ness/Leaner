import Mathlib

variable {α : Type*}

theorem unop_ratCast [RatCast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q := rfl

