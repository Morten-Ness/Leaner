import Mathlib

variable {α : Type u}

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

theorem lt_inv_self_iff : a < a⁻¹ ↔ a < 1 := by contrapose!; exact inv_le_self_iff

