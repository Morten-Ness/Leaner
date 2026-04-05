import Mathlib

variable {α : Type u} {β : Type v}

theorem ofMul_pow [Monoid α] (n : ℕ) (a : α) : Additive.ofMul (a ^ n) = n • Additive.ofMul a := rfl

