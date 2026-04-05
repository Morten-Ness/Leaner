import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g ≤ h) : f ≤ h := hgh.elim (Or.inl ∘ CauSeq.lt_of_eq_of_lt hfg) (Or.inr ∘ Setoid.trans hfg)

