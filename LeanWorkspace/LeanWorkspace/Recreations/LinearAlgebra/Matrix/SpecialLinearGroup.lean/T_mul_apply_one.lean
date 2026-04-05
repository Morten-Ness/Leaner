import Mathlib

theorem T_mul_apply_one (g : SL(2, ℤ)) : (ModularGroup.T * g) 1 = g 1 := by
  simpa using ModularGroup.T_pow_mul_apply_one 1 g

