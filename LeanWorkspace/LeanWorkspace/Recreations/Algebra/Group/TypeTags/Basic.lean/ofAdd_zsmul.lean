import Mathlib

variable {α : Type u} {β : Type v}

theorem ofAdd_zsmul [SubNegMonoid α] (z : ℤ) (a : α) : Multiplicative.ofAdd (z • a) = Multiplicative.ofAdd a ^ z := rfl

