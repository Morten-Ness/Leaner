import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sup_eq_left {a b : CauSeq α abs} (h : b ≤ a) : a ⊔ b ≈ a := by
  simpa only [CauSeq.sup_comm] using CauSeq.sup_eq_right h

