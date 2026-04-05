import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem lt_div_iff_of_neg' (hc : c < 0) : a < b / c ↔ b < c * a := by
  rw [mul_comm, lt_div_iff_of_neg hc]

