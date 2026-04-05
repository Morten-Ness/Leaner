import Mathlib

variable {α : Type u}

variable [Group α]

variable [LT α] [MulRightStrictMono α] {a b c : α}

theorem Right.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_right a, inv_mul_cancel, one_mul]

