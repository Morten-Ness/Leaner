import Mathlib

variable {α : Type u}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a b : α}

theorem inv_le_inv' : a ≤ b → b⁻¹ ≤ a⁻¹ := inv_le_inv_iff.mpr

