import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0 := let ⟨u, hu⟩ := hb
  hu ▸ Units.mul_left_eq_zero u

