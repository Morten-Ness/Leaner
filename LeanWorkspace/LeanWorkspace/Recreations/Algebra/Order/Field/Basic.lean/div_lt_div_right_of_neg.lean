import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a := by
  rw [div_lt_iff_of_neg hc, div_mul_cancel₀ _ hc.ne]

