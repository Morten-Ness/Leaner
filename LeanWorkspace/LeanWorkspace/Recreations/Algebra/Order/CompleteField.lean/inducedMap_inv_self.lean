import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

variable {α β} {a : α} {b : β} {q : ℚ}

theorem inducedMap_inv_self (b : β) : ConditionallyCompleteLinearOrderedField.inducedMap γ β (ConditionallyCompleteLinearOrderedField.inducedMap β γ b) = b := by
  rw [ConditionallyCompleteLinearOrderedField.inducedMap_inducedMap, ConditionallyCompleteLinearOrderedField.inducedMap_self]

