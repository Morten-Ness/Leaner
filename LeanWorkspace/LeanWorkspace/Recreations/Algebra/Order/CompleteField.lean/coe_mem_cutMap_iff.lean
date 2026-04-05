import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Field α] [LinearOrder α]

variable (β) [DivisionRing β] {a a₁ a₂ : α} {b : β} {q : ℚ}

theorem coe_mem_cutMap_iff [CharZero β] : (q : β) ∈ LinearOrderedField.cutMap β a ↔ (q : α) < a := Rat.cast_injective.mem_set_image

