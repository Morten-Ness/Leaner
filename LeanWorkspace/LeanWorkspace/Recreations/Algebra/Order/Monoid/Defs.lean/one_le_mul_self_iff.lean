import Mathlib

variable {α : Type*}

variable [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

theorem one_le_mul_self_iff : 1 ≤ a * a ↔ 1 ≤ a := ⟨fun h ↦ by contrapose! h; exact mul_lt_one' h h, fun h ↦ one_le_mul h h⟩

