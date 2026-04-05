import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a b x : G₀}

theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b := calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

