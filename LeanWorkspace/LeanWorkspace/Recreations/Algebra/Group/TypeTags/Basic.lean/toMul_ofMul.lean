import Mathlib

variable {α : Type u} {β : Type v}

theorem toMul_ofMul (x : α) : (Additive.ofMul x).toMul = x := rfl

