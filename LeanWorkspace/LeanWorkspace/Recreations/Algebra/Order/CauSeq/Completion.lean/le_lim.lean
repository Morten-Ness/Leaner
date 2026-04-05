import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [IsComplete α abs]

theorem le_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x ≤ f) : x ≤ CauSeq.lim f := CauSeq.const_le.1 <| CauSeq.le_of_le_of_eq h (CauSeq.equiv_lim f)

