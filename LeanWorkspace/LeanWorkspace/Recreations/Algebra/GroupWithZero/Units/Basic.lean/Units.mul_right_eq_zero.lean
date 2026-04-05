import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 := ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right (u : M₀)⟩

