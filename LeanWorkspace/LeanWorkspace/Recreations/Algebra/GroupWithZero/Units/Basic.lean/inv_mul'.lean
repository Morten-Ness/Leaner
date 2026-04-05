import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

theorem inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 := inv_mul_cancel₀ Units.ne_zero u

