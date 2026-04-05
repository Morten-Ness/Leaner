import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem inf_le_left {a b : CauSeq α abs} : a ⊓ b ≤ a := CauSeq.le_of_exists ⟨0, fun _ _ => inf_le_left⟩

