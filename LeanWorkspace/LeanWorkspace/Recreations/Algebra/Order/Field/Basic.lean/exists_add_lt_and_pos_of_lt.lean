import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem exists_add_lt_and_pos_of_lt (h : b < a) : ∃ c, b + c < a ∧ 0 < c := ⟨(a - b) / 2, add_sub_div_two_lt h, div_pos (sub_pos_of_lt h) zero_lt_two⟩

