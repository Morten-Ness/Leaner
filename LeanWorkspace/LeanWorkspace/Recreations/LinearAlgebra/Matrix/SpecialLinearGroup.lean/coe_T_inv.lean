import Mathlib

theorem coe_T_inv : ↑(ModularGroup.T⁻¹) = !![1, -1; 0, 1] := by simp [Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_T, adjugate_fin_two]

