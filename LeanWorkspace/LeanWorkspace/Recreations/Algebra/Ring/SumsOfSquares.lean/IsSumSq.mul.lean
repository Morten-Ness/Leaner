import Mathlib

variable {R : Type*}

theorem IsSumSq.mul [NonUnitalCommSemiring R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ * s₂) := by
  simpa using mul_mem (by simpa : _ ∈ NonUnitalSubsemiring.sumSq R) (by simpa)

