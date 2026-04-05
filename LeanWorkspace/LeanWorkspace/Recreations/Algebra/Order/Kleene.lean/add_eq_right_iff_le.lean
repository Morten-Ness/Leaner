import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [IdemSemiring α] {a b c : α}

theorem add_eq_right_iff_le : a + b = b ↔ a ≤ b := by simp

alias ⟨_, LE.le.add_eq_left⟩ := add_eq_left_iff_le

alias ⟨_, LE.le.add_eq_right⟩ := add_eq_right_iff_le

