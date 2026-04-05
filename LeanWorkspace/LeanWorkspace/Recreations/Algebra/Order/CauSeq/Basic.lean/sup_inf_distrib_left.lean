import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sup_inf_distrib_left (a b c : CauSeq α abs) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := CauSeq.ext fun _ ↦ max_min_distrib_left _ _ _

