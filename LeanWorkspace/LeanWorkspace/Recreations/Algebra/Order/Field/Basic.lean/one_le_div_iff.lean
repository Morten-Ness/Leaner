import Mathlib

variable {ι α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d : α} {n : ℤ}

theorem one_le_div_iff : 1 ≤ a / b ↔ 0 < b ∧ b ≤ a ∨ b < 0 ∧ a ≤ b := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, one_le_div_of_neg]
  · simp [zero_lt_one.not_ge]
  · simp [hb, hb.not_gt, one_le_div]

