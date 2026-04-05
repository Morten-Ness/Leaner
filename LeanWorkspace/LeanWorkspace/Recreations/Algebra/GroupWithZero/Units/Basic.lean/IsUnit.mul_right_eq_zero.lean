import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0 := let ⟨u, hu⟩ := ha
  hu ▸ Units.mul_right_eq_zero u

