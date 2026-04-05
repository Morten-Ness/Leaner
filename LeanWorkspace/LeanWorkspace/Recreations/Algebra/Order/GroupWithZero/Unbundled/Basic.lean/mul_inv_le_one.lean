import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [Preorder G₀] [ZeroLEOneClass G₀] {a b c : G₀}

theorem mul_inv_le_one : a * a⁻¹ ≤ 1 := by simpa only [div_eq_mul_inv] using div_self_le_one a

