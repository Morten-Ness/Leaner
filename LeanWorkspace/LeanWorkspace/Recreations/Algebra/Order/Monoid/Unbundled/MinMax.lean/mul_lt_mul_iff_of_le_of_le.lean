import Mathlib

variable {α β : Type*}

variable [LinearOrder α]

variable [Mul α]

theorem mul_lt_mul_iff_of_le_of_le [MulLeftMono α]
    [MulRightMono α] [MulLeftStrictMono α]
    [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂)
    (hb : b₁ ≤ b₂) : a₁ * b₁ < a₂ * b₂ ↔ a₁ < a₂ ∨ b₁ < b₂ := by
  refine ⟨lt_or_lt_of_mul_lt_mul, fun h => ?_⟩
  rcases h with ha' | hb'
  · exact mul_lt_mul_of_lt_of_le ha' hb
  · exact mul_lt_mul_of_le_of_lt ha hb'

