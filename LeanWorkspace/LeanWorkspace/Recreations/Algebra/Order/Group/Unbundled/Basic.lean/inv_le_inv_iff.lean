import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulLeftMono α] {a b c d : α}

variable [MulRightMono α]

theorem inv_le_inv_iff : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [← mul_le_mul_iff_left a, ← mul_le_mul_iff_right b]
  simp

alias ⟨le_of_neg_le_neg, _⟩ := neg_le_neg_iff

