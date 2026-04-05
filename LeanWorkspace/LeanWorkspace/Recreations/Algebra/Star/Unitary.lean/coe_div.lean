import Mathlib

variable {R : Type*}

variable [GroupWithZero R] [StarMul R]

theorem coe_div (U₁ U₂ : unitary R) : ↑(U₁ / U₂) = (U₁ / U₂ : R) := by
  simp only [div_eq_mul_inv, Unitary.coe_inv, Submonoid.coe_mul]

