import Mathlib

variable {α : Type u} {β : Type v}

theorem ofAdd_nsmul [AddMonoid α] (n : ℕ) (a : α) : Multiplicative.ofAdd (n • a) = Multiplicative.ofAdd a ^ n := rfl

