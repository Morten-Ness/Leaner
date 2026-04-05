import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem lt_inf {a b c : CauSeq α abs} (hb : a < b) (hc : a < c) : a < b ⊓ c := by
  obtain ⟨⟨εb, εb0, ib, hb⟩, ⟨εc, εc0, ic, hc⟩⟩ := hb, hc
  refine ⟨εb ⊓ εc, lt_inf_iff.mpr ⟨εb0, εc0⟩, ib ⊔ ic, fun i hi => ?_⟩
  have := min_le_min (hb _ (sup_le_iff.mp hi).1) (hc _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_right _ _ _)

