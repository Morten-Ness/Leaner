import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_of_isUnit {x : M₀} (h : IsUnit x) : x⁻¹ʳ = ((h.unit⁻¹ : M₀ˣ) : M₀) := dif_pos h

