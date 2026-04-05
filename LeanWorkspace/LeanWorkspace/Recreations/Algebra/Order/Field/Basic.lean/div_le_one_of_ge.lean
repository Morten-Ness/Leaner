import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem div_le_one_of_ge (h : b ≤ a) (hb : b ≤ 0) : a / b ≤ 1 := by
  simpa only [neg_div_neg_eq] using div_le_one_of_le₀ (neg_le_neg h) (neg_nonneg_of_nonpos hb)

