import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mul_mono {a b c d : Associates M} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d := let ⟨x, hx⟩ := h₁
  let ⟨y, hy⟩ := h₂
  ⟨x * y, by simp [hx, hy, mul_comm, mul_left_comm]⟩

