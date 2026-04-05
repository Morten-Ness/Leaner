import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem inf_eq_left {a b : CauSeq α abs} (h : a ≤ b) : a ⊓ b ≈ a := by
  simpa only [CauSeq.inf_comm] using CauSeq.inf_eq_right h

