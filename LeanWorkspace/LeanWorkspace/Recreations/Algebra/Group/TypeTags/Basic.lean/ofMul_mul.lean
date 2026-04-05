import Mathlib

variable {α : Type u} {β : Type v}

theorem ofMul_mul [Mul α] (x y : α) : Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y := rfl

