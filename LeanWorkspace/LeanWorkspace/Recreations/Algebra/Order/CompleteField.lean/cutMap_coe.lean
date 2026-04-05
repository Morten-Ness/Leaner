import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Field α] [LinearOrder α]

variable (β) [IsStrictOrderedRing α] [Field β] [LinearOrder β] [IsStrictOrderedRing β]
  {a a₁ a₂ : α} {b : β} {q : ℚ}

theorem cutMap_coe (q : ℚ) : LinearOrderedField.cutMap β (q : α) = Rat.cast '' {r : ℚ | (r : β) < q} := by
  simp_rw [LinearOrderedField.cutMap, Rat.cast_lt]

