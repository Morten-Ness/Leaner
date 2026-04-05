import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem const_le {x y : α} : CauSeq.const x ≤ CauSeq.const y ↔ x ≤ y := by
  rw [le_iff_lt_or_eq]; exact or_congr CauSeq.const_lt CauSeq.const_equiv

