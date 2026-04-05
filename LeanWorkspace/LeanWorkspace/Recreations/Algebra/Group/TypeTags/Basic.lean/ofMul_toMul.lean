import Mathlib

variable {α : Type u} {β : Type v}

theorem ofMul_toMul (x : Additive α) : Additive.ofMul x.toMul = x := rfl

