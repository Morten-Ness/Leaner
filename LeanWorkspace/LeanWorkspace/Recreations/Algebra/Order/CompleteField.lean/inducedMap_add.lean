import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

variable {α β} {a : α} {b : β} {q : ℚ}

theorem inducedMap_add (x y : α) :
    ConditionallyCompleteLinearOrderedField.inducedMap α β (x + y) = ConditionallyCompleteLinearOrderedField.inducedMap α β x + ConditionallyCompleteLinearOrderedField.inducedMap α β y := by
  rw [ConditionallyCompleteLinearOrderedField.inducedMap, LinearOrderedField.cutMap_add]
  exact csSup_add (LinearOrderedField.cutMap_nonempty β x) (LinearOrderedField.cutMap_bddAbove β x) (LinearOrderedField.cutMap_nonempty β y)
    (LinearOrderedField.cutMap_bddAbove β y)

