import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem le_sup_right {a b : CauSeq α abs} : b ≤ a ⊔ b := CauSeq.le_of_exists ⟨0, fun _ _ => le_sup_right⟩

