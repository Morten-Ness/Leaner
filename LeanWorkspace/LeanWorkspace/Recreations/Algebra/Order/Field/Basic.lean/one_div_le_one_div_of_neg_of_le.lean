import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  rwa [div_le_iff_of_neg' hb, ← div_eq_mul_one_div, div_le_one_of_neg (h.trans_lt hb)]

