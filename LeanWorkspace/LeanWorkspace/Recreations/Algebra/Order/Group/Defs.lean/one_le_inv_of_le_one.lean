import Mathlib

variable {α : Type u}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a b : α}

theorem one_le_inv_of_le_one : a ≤ 1 → 1 ≤ a⁻¹ := one_le_inv'.mpr

