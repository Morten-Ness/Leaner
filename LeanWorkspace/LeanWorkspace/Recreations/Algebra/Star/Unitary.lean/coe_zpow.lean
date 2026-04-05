import Mathlib

variable {R : Type*}

variable [GroupWithZero R] [StarMul R]

theorem coe_zpow (U : unitary R) (z : ℤ) : ↑(U ^ z) = (U : R) ^ z := by
  cases z
  · simp [SubmonoidClass.coe_pow]
  · simp [Unitary.coe_inv]

