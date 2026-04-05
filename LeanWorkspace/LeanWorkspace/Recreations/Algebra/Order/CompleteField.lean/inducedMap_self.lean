import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

variable {α β} {a : α} {b : β} {q : ℚ}

theorem inducedMap_self (b : β) : ConditionallyCompleteLinearOrderedField.inducedMap β β b = b := eq_of_forall_rat_lt_iff_lt fun _ => ConditionallyCompleteLinearOrderedField.coe_lt_inducedMap_iff

