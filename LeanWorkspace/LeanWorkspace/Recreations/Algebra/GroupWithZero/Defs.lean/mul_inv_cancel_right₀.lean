import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b * b⁻¹ = a := calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]

