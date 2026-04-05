import Mathlib

variable {α : Type u} {β : Type v}

theorem ofMul_one [One α] : @Additive.ofMul α 1 = 0 := rfl

