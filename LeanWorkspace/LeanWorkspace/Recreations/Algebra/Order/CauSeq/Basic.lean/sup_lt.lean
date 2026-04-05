import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sup_lt {a b c : CauSeq α abs} (ha : a < c) (hb : b < c) : a ⊔ b < c := by
  obtain ⟨⟨εa, εa0, ia, ha⟩, ⟨εb, εb0, ib, hb⟩⟩ := ha, hb
  refine ⟨εa ⊓ εb, lt_inf_iff.mpr ⟨εa0, εb0⟩, ia ⊔ ib, fun i hi => ?_⟩
  have := min_le_min (ha _ (sup_le_iff.mp hi).1) (hb _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_left _ _ _)

