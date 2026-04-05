import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sup_idem (a : CauSeq α abs) : a ⊔ a = a := Subtype.ext (sup_idem _)

