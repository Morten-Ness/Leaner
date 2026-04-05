import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

variable {α β} {a : α} {b : β} {q : ℚ}

theorem inducedMap_nonneg (ha : 0 ≤ a) : 0 ≤ ConditionallyCompleteLinearOrderedField.inducedMap α β a := (ConditionallyCompleteLinearOrderedField.inducedMap_zero α _).ge.trans <| ConditionallyCompleteLinearOrderedField.inducedMap_mono _ _ ha

