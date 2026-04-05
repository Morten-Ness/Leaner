import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [GroupWithZero G₀] [GroupWithZero G₀'] [MulActionWithZero G₀ G₀']
  [SMulCommClass G₀ G₀' G₀'] [IsScalarTower G₀ G₀' G₀']

theorem smul_inv₀ (c : G₀) (x : G₀') : (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp only [inv_zero, zero_smul]
  obtain rfl | hx := eq_or_ne x 0
  · simp only [inv_zero, smul_zero]
  · refine inv_eq_of_mul_eq_one_left ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, inv_mul_cancel₀ hx, one_smul]

