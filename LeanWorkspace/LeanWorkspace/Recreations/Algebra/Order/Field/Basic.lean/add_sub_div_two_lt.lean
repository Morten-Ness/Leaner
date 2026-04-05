import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem add_sub_div_two_lt (h : a < b) : a + (b - a) / 2 < b := by
  rwa [← div_sub_div_same, sub_eq_add_neg, add_comm (b / 2), ← add_assoc, ← sub_eq_add_neg, ←
    lt_sub_iff_add_lt, sub_self_div_two, sub_self_div_two,
    div_lt_div_iff_of_pos_right (zero_lt_two' α)]

