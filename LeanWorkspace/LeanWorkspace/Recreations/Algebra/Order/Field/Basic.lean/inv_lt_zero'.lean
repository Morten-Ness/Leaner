import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem inv_lt_zero' : a⁻¹ < 0 ↔ a < 0 := by
  rw [← neg_pos, ← inv_neg, inv_pos, neg_pos]

