import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sup_inf_distrib_right (a b c : CauSeq α abs) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) := CauSeq.ext fun _ ↦ max_min_distrib_right _ _ _

