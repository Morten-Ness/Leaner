import Mathlib

theorem T_pow_mul_apply_one (n : ℤ) (g : SL(2, ℤ)) : (ModularGroup.T ^ n * g) 1 = g 1 := by
  ext j
  simp [ModularGroup.coe_T_zpow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

