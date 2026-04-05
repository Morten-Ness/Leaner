import Mathlib

variable {α β : Type*}

variable [LinearOrder α]

variable [Mul α]

theorem lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ < a₂ * b₂ → a₁ < a₂ ∨ b₁ < b₂ := by
  contrapose!
  exact fun h => mul_le_mul' h.1 h.2

