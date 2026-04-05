import Mathlib

variable {α : Type u} {β : Type v}

theorem ofMul_zpow [DivInvMonoid α] (z : ℤ) (a : α) : Additive.ofMul (a ^ z) = z • Additive.ofMul a := rfl

