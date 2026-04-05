import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem le_sup_left {a b : CauSeq α abs} : a ≤ a ⊔ b := CauSeq.le_of_exists ⟨0, fun _ _ => le_sup_left⟩

