import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem lt_trans {f g h : CauSeq α abs} (fg : f < g) (gh : g < h) : f < h := show CauSeq.Pos (h - f) by
    convert CauSeq.add_pos fg gh using 1
    simp

