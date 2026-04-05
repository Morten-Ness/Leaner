import Mathlib

variable {α : Type u} {β : Type v}

theorem toMul_zero [One α] : (0 : Additive α).toMul = 1 := rfl

