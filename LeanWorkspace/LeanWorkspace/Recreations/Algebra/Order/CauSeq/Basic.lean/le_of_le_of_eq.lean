import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f ≤ g) (hgh : g ≈ h) : f ≤ h := hfg.elim (fun h => Or.inl (CauSeq.lt_of_lt_of_eq h hgh)) fun h => Or.inr (Setoid.trans h hgh)

