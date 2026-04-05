import Mathlib

variable {R : Type*}

theorem IsSumNonzeroSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
    (h₁ : IsSumNonzeroSq s₁) (h₂ : IsSumNonzeroSq s₂) : IsSumNonzeroSq (s₁ + s₂) := by
  induction h₁ <;> simp_all [sq_add, add_assoc]

