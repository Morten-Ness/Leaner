import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [IsComplete α abs]

theorem lim_lt {f : CauSeq α abs} {x : α} (h : f < CauSeq.const abs x) : CauSeq.lim f < x := CauSeq.const_lt.1 <| CauSeq.lt_of_eq_of_lt (Setoid.symm (CauSeq.equiv_lim f)) h

