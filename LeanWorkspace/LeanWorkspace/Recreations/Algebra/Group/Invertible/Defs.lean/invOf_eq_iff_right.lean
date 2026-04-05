import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_eq_iff_right [Invertible a] : ⅟a = b ↔ a * b = 1 := ⟨fun h ↦ by rw [← h, mul_invOf_self], invOf_eq_right_inv⟩

