import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sup_comm (a b : CauSeq α abs) : a ⊔ b = b ⊔ a := Subtype.ext (sup_comm _ _)

