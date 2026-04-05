import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 := ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩

