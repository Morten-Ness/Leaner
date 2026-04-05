import Mathlib

variable {α : Type u} {β : Type v}

theorem ofMul_inv [Inv α] (x : α) : Additive.ofMul x⁻¹ = -Additive.ofMul x := rfl

