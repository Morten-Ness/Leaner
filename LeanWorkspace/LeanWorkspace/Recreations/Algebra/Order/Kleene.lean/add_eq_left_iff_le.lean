import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [IdemSemiring α] {a b c : α}

theorem add_eq_left_iff_le : a + b = a ↔ b ≤ a := by simp

