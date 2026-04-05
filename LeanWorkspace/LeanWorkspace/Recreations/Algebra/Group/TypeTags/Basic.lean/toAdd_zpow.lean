import Mathlib

variable {α : Type u} {β : Type v}

theorem toAdd_zpow [SubNegMonoid α] (a : Multiplicative α) (z : ℤ) : (a ^ z).toAdd = z • a.toAdd := rfl

