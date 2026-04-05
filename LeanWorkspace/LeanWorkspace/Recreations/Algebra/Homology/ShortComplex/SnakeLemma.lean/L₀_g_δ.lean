import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem L₀_g_δ : S.L₀.g ≫ S.δ = 0 := by
  rw [← CategoryTheory.ShortComplex.SnakeInput.L₀X₂ToP_comp_pullback_snd, assoc]
  erw [S.L₀'_exact.g_desc]
  rw [L₀X₂ToP_comp_φ₁_assoc, zero_comp]

