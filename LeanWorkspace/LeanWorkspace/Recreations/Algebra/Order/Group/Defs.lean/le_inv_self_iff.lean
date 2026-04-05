import Mathlib

variable {α : Type u}

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

theorem le_inv_self_iff : a ≤ a⁻¹ ↔ a ≤ 1 := by contrapose!; exact inv_lt_self_iff

