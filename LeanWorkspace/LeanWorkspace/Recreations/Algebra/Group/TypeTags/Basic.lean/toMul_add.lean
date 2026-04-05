import Mathlib

variable {α : Type u} {β : Type v}

theorem toMul_add [Mul α] (x y : Additive α) : (x + y).toMul = x.toMul * y.toMul := rfl

