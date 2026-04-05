import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a := div_lt_div_iff_of_pos_left zero_lt_one ha hb

