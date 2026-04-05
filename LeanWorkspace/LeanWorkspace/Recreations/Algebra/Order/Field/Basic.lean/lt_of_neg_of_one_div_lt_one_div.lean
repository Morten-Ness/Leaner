import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem lt_of_neg_of_one_div_lt_one_div (hb : b < 0) (h : 1 / a < 1 / b) : b < a := by
  simpa using one_div_lt_one_div_of_neg_of_lt (one_div b ▸ inv_lt_zero'.2 hb) h

