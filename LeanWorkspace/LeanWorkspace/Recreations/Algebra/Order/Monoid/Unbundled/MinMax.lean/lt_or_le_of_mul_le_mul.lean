import Mathlib

variable {α β : Type*}

variable [LinearOrder α]

variable [Mul α]

theorem lt_or_le_of_mul_le_mul [MulLeftStrictMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ < a₂ ∨ b₁ ≤ b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_le_of_lt h.1 h.2

