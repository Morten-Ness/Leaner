import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem inf_comm (a b : CauSeq α abs) : a ⊓ b = b ⊓ a := Subtype.ext (inf_comm _ _)

