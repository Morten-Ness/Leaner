import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

theorem inducedMap_rat (q : ℚ) : ConditionallyCompleteLinearOrderedField.inducedMap α β (q : α) = q := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (LinearOrderedField.cutMap_nonempty β (q : α)) (fun x h => ?_) fun w h => ?_
  · rw [LinearOrderedField.cutMap_coe] at h
    obtain ⟨r, h, rfl⟩ := h
    exact le_of_lt h
  · obtain ⟨q', hwq, hq⟩ := exists_rat_btwn h
    rw [LinearOrderedField.cutMap_coe]
    exact ⟨q', ⟨_, hq, rfl⟩, hwq⟩

