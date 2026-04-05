import Mathlib

variable {α : Type*}

variable [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

theorem mul_self_le_one_iff : a * a ≤ 1 ↔ a ≤ 1 := by contrapose!; exact one_lt_mul_self_iff

