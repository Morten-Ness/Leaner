import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a b x : G₀}

theorem inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b⁻¹ * b = a := calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]

