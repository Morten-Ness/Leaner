import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Field α] [LinearOrder α]

variable (β) [DivisionRing β] {a a₁ a₂ : α} {b : β} {q : ℚ}

theorem mem_cutMap_iff : b ∈ LinearOrderedField.cutMap β a ↔ ∃ q : ℚ, (q : α) < a ∧ (q : β) = b := Iff.rfl

