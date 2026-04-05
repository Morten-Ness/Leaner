import Mathlib

variable {α : Type u} {β : Type v}

theorem toMul_neg [Inv α] (x : Additive α) : (-x).toMul = x.toMul⁻¹ := rfl

