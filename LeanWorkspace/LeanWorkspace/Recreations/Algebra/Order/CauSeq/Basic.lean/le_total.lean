import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem le_total (f g : CauSeq α abs) : f ≤ g ∨ g ≤ f := (or_assoc.2 (CauSeq.lt_total f g)).imp_right Or.inl

