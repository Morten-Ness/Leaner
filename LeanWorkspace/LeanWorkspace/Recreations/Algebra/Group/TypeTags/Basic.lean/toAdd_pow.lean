import Mathlib

variable {α : Type u} {β : Type v}

theorem toAdd_pow [AddMonoid α] (a : Multiplicative α) (n : ℕ) : (a ^ n).toAdd = n • a.toAdd := rfl

