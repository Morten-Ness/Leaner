import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Field α] [LinearOrder α]

variable (β) [DivisionRing β] {a a₁ a₂ : α} {b : β} {q : ℚ}

theorem cutMap_mono (h : a₁ ≤ a₂) : LinearOrderedField.cutMap β a₁ ⊆ LinearOrderedField.cutMap β a₂ := image_mono fun _ => h.trans_lt'

