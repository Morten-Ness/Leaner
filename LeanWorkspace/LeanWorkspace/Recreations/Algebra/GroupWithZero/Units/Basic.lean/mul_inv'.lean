import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

theorem mul_inv' (u : G₀ˣ) : u * (u : G₀)⁻¹ = 1 := mul_inv_cancel₀ Units.ne_zero u

