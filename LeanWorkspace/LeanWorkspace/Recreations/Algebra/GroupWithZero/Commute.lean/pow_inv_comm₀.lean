import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

theorem pow_inv_comm₀ (a : G₀) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m := Commute.inv_left₀ (Commute.refl a).pow_pow m n

