import Mathlib

variable {α : Type u}

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

theorem inv_lt_self_iff : a⁻¹ < a ↔ 1 < a := by simp [inv_lt_iff_one_lt_mul]

