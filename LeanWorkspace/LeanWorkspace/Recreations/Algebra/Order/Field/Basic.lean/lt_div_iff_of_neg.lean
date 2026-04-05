import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem lt_div_iff_of_neg (hc : c < 0) : a < b / c ↔ b < a * c := by
  rw [← neg_neg c, mul_neg, div_neg, lt_neg, div_lt_iff₀ (neg_pos.2 hc), neg_mul]

