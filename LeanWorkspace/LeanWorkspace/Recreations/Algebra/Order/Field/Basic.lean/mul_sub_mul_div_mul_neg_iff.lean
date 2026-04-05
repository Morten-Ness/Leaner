import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

omit [PosMulReflectLT α] in
theorem mul_sub_mul_div_mul_neg_iff (hc : c ≠ 0) (hd : d ≠ 0) :
    (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d := by
  rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_lt_zero]

