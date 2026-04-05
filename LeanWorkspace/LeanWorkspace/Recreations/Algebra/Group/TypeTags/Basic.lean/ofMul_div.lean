import Mathlib

variable {α : Type u} {β : Type v}

theorem ofMul_div [Div α] (x y : α) : Additive.ofMul (x / y) = Additive.ofMul x - Additive.ofMul y := rfl

