import Mathlib

variable {α : Type u} {β : Type v}

theorem toMul_sub [Div α] (x y : Additive α) : (x - y).toMul = x.toMul / y.toMul := rfl

