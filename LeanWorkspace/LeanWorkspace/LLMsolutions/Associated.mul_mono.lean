import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mul_mono {a b c d : Associates M} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d := by
  rcases h₁ with ⟨x, rfl⟩
  rcases h₂ with ⟨y, rfl⟩
  refine ⟨x * y, ?_⟩
  simp [mul_assoc, mul_left_comm, mul_comm]
