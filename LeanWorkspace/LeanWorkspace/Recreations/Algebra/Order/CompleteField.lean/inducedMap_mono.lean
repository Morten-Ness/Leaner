import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

theorem inducedMap_mono : Monotone (ConditionallyCompleteLinearOrderedField.inducedMap α β) := fun _ _ h =>
  csSup_le_csSup (LinearOrderedField.cutMap_bddAbove β _) (LinearOrderedField.cutMap_nonempty β _) (LinearOrderedField.cutMap_mono β h)

