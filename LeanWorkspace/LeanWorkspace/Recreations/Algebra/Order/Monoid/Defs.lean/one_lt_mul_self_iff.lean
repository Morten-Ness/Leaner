import Mathlib

variable {α : Type*}

variable [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] {a : α}

theorem one_lt_mul_self_iff : 1 < a * a ↔ 1 < a := ⟨fun h ↦ by contrapose! h; exact mul_le_one' h h, fun h ↦ one_lt_mul'' h h⟩

