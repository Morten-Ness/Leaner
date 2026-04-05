import Mathlib

variable {α : Type u}

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

theorem inv_le_self_iff : a⁻¹ ≤ a ↔ 1 ≤ a := by simp [inv_le_iff_one_le_mul']

