import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem IsUnit.ringInverse {a : M₀} : IsUnit a → IsUnit a⁻¹ʳ
  | ⟨u, hu⟩ => hu ▸ ⟨u⁻¹, (Ring.inverse_unit u).symm⟩
