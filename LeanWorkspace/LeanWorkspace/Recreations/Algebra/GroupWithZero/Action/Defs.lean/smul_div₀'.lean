import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [Group α] [GroupWithZero β] [MulDistribMulAction α β]

theorem smul_div₀' (g : α) (x y : β) : g • (x / y) = (g • x) / (g • y) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, smul_mul', smul_inv₀']

