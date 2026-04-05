import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem lt_of_eq_of_lt {f g h : CauSeq α abs} (fg : f ≈ g) (gh : g < h) : f < h := by
  have := CauSeq.pos_add_limZero gh (CauSeq.neg_limZero fg)
  rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this

