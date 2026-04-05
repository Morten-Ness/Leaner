import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Field α] [LinearOrder α]

variable (β) [DivisionRing β] {a a₁ a₂ : α} {b : β} {q : ℚ}

theorem cutMap_self (a : α) : LinearOrderedField.cutMap α a = Iio a ∩ Set.range (Rat.cast : ℚ → α) := by
  grind [LinearOrderedField.mem_cutMap_iff]

