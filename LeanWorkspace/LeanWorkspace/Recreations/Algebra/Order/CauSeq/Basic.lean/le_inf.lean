import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem le_inf {a b c : CauSeq α abs} (hb : a ≤ b) (hc : a ≤ c) : a ≤ b ⊓ c := by
  obtain hb | hb := hb
  · obtain hc | hc := hc
    · exact Or.inl (CauSeq.lt_inf hb hc)
    · replace hb := CauSeq.le_of_eq_of_le (Setoid.symm hc) hb.le
      refine CauSeq.le_of_eq_of_le hc (Or.inr ?_)
      exact Setoid.symm (CauSeq.inf_eq_right hb)
  · replace hc := CauSeq.le_of_eq_of_le (Setoid.symm hb) hc
    refine CauSeq.le_of_eq_of_le hb (Or.inr ?_)
    exact Setoid.symm (CauSeq.inf_eq_left hc)

