import Mathlib

variable {M₀ M₀' : Type*} [MulZeroOneClass M₀] [Nontrivial M₀]

variable {G₀ : Type*} [GroupWithZero G₀] {a : G₀}

theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
  simpa [a_eq_0] using mul_inv_cancel₀ h

