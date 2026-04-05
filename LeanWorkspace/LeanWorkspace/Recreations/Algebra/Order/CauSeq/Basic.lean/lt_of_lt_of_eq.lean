import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h) : f < h := show CauSeq.Pos (h - f) by
    convert CauSeq.pos_add_limZero fg (CauSeq.neg_limZero gh) using 1
    simp

