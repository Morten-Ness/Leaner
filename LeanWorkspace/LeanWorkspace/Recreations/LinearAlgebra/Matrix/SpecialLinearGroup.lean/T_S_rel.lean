import Mathlib

theorem T_S_rel : ModularGroup.S • ModularGroup.S • ModularGroup.S • ModularGroup.T • ModularGroup.S • ModularGroup.T • ModularGroup.S = ModularGroup.T⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

