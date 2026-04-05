import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [IsComplete α abs]

theorem lt_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x < f) : x < CauSeq.lim f := CauSeq.const_lt.1 <| CauSeq.lt_of_lt_of_eq h (CauSeq.equiv_lim f)

