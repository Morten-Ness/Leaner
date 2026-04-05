import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem div_lt_iff_of_neg' (hc : c < 0) : b / c < a ↔ c * a < b := by
  rw [mul_comm, div_lt_iff_of_neg hc]

