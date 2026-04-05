import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem one_le_div_of_neg (hb : b < 0) : 1 ≤ a / b ↔ a ≤ b := by rw [le_div_iff_of_neg hb, one_mul]

