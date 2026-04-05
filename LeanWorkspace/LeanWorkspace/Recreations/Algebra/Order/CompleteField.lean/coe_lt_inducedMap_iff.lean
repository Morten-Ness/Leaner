import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

variable {α β} {a : α} {b : β} {q : ℚ}

theorem coe_lt_inducedMap_iff : (q : β) < ConditionallyCompleteLinearOrderedField.inducedMap α β a ↔ (q : α) < a := by
  refine ⟨fun h => ?_, fun hq => ?_⟩
  · rw [← ConditionallyCompleteLinearOrderedField.inducedMap_rat α] at h
    exact (ConditionallyCompleteLinearOrderedField.inducedMap_mono α β).reflect_lt h
  · obtain ⟨q', hq, hqa⟩ := exists_rat_btwn hq
    apply lt_csSup_of_lt (LinearOrderedField.cutMap_bddAbove β a) (LinearOrderedField.coe_mem_cutMap_iff.mpr hqa)
    exact mod_cast hq

