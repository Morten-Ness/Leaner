import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem δ_L₃_f : S.δ ≫ S.L₃.f = 0 := by
  rw [← cancel_epi S.L₀'.g]
  erw [S.L₀'_exact.g_desc_assoc]
  simp [S.v₂₃.comm₁₂, CategoryTheory.ShortComplex.SnakeInput.φ₂]

