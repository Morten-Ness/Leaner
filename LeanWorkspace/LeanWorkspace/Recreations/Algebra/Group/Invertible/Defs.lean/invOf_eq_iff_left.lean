import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_eq_iff_left [Invertible a] : ⅟a = b ↔ b * a = 1 := ⟨fun h ↦ by rw [← h, invOf_mul_self], invOf_eq_left_inv⟩

