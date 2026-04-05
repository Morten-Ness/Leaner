import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

theorem inducedMap_zero : ConditionallyCompleteLinearOrderedField.inducedMap α β 0 = 0 := mod_cast ConditionallyCompleteLinearOrderedField.inducedMap_rat α β 0

