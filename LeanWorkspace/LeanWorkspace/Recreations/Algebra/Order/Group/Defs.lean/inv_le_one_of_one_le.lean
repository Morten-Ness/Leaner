import Mathlib

variable {α : Type u}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a b : α}

theorem inv_le_one_of_one_le : 1 ≤ a → a⁻¹ ≤ 1 := inv_le_one'.mpr

