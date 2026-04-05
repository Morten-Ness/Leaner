import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

theorem mul_inv_cancel₀ (h : a ≠ 0) : a * a⁻¹ = 1 := GroupWithZero.mul_inv_cancel a h

-- See note [lower instance priority]

