import Mathlib

variable {ι α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d : α} {n : ℤ}

theorem div_le_one_iff : a / b ≤ 1 ↔ 0 < b ∧ a ≤ b ∨ b = 0 ∨ b < 0 ∧ b ≤ a := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, hb.ne, div_le_one_of_neg]
  · simp [zero_le_one]
  · simp [hb, hb.not_gt, div_le_one, hb.ne.symm]

