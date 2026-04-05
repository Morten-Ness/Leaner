import Mathlib

variable {α : Type u}

variable [Group α]

variable [LE α] [MulRightMono α] {a b c : α}

theorem Right.one_le_inv_iff : 1 ≤ a⁻¹ ↔ a ≤ 1 := by
  rw [← mul_le_mul_iff_right a]
  simp

