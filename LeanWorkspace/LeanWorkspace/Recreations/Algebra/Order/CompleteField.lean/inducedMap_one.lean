import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

theorem inducedMap_one : ConditionallyCompleteLinearOrderedField.inducedMap α β 1 = 1 := mod_cast ConditionallyCompleteLinearOrderedField.inducedMap_rat α β 1

