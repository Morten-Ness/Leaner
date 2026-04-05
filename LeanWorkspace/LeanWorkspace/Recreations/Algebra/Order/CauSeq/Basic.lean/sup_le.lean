import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sup_le {a b c : CauSeq α abs} (ha : a ≤ c) (hb : b ≤ c) : a ⊔ b ≤ c := by
  obtain ha | ha := ha
  · obtain hb | hb := hb
    · exact Or.inl (CauSeq.sup_lt ha hb)
    · replace ha := CauSeq.le_of_le_of_eq ha.le (Setoid.symm hb)
      refine CauSeq.le_of_le_of_eq (Or.inr ?_) hb
      exact CauSeq.sup_eq_right ha
  · replace hb := CauSeq.le_of_le_of_eq hb (Setoid.symm ha)
    refine CauSeq.le_of_le_of_eq (Or.inr ?_) ha
    exact CauSeq.sup_eq_left hb

