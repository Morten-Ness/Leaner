import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem one_div_le_neg_one (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 := suffices 1 / a ≤ 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_le_one_div_of_neg_of_le h1 h2

