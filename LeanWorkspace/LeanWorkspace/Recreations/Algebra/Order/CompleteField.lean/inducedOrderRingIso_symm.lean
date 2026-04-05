import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

variable {α β} {a : α} {b : β} {q : ℚ}

theorem inducedOrderRingIso_symm : (ConditionallyCompleteLinearOrderedField.inducedOrderRingIso β γ).symm = ConditionallyCompleteLinearOrderedField.inducedOrderRingIso γ β := rfl

