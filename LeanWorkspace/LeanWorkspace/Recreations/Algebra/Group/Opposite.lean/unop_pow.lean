import Mathlib

variable {α : Type*}

theorem unop_pow {β} [Pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b := rfl

