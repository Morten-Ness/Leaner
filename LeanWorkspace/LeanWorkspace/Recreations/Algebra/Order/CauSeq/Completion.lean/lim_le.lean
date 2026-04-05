import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [IsComplete α abs]

theorem lim_le {f : CauSeq α abs} {x : α} (h : f ≤ CauSeq.const abs x) : CauSeq.lim f ≤ x := CauSeq.const_le.1 <| CauSeq.le_of_eq_of_le (Setoid.symm (CauSeq.equiv_lim f)) h

