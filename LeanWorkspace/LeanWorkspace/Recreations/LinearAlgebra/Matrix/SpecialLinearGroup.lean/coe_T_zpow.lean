import Mathlib

theorem coe_T_zpow (n : ℤ) : (ModularGroup.T ^ n).1 = !![1, n; 0, 1] := by
  induction n with
  | zero => rw [zpow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  | succ n h =>
    simp_rw [zpow_add, zpow_one, Matrix.SpecialLinearGroup.coe_mul, h, ModularGroup.coe_T, Matrix.mul_fin_two]
    congrm !![_, ?_; _, _]
    rw [mul_one, mul_one, add_comm]
  | pred n h =>
    simp_rw [zpow_sub, zpow_one, Matrix.SpecialLinearGroup.coe_mul, h, ModularGroup.coe_T_inv, Matrix.mul_fin_two]
    congrm !![?_, ?_; _, _] <;> ring

