import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem inf_idem (a : CauSeq α abs) : a ⊓ a = a := Subtype.ext (inf_idem _)

