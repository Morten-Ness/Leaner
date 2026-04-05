import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) : a * (a⁻¹ * b) = b := calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

