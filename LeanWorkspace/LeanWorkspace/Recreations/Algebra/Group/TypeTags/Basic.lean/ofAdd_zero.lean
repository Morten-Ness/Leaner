import Mathlib

variable {α : Type u} {β : Type v}

theorem ofAdd_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1 := rfl

