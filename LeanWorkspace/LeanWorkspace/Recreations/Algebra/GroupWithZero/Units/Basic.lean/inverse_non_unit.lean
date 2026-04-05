import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ = 0 := dif_neg h

