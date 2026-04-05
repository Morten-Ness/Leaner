import Mathlib

variable {M₀ M₀' : Type*} [MulZeroOneClass M₀] [Nontrivial M₀]

variable {G₀ : Type*} [GroupWithZero G₀] {a : G₀}

theorem inv_mul_cancel₀ (h : a ≠ 0) : a⁻¹ * a = 1 := calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]

