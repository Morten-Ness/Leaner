import Mathlib

variable {R : Type*} [CommRing R] {a b x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n : R}

theorem sq_add_mul_sq_mul_sq_add_mul_sq :
    (x₁ ^ 2 + n * x₂ ^ 2) * (y₁ ^ 2 + n * y₂ ^ 2) =
    (x₁ * y₁ - n * x₂ * y₂) ^ 2 + n * (x₁ * y₂ + x₂ * y₁) ^ 2 := by
  ring

