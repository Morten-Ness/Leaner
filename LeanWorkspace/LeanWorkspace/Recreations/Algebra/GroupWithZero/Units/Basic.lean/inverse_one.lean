import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_one : (1 : M₀)⁻¹ʳ = 1 := Ring.inverse_unit 1

