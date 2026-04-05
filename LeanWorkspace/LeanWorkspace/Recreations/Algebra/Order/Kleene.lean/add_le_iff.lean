import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [IdemSemiring α] {a b c : α}

theorem add_le_iff : a + b ≤ c ↔ a ≤ c ∧ b ≤ c := by simp

