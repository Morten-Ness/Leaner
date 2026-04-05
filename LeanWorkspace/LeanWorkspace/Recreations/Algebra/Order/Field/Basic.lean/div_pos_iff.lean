import Mathlib

variable {ι α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d : α} {n : ℤ}

theorem div_pos_iff : 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  simp only [division_def, mul_pos_iff, inv_pos, inv_lt_zero]

