import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem L₀X₂ToP_comp_φ₁ : S.L₀X₂ToP ≫ S.φ₁ = 0 := by
  simp only [← cancel_mono S.L₂.f, CategoryTheory.ShortComplex.SnakeInput.L₀X₂ToP, assoc, CategoryTheory.ShortComplex.SnakeInput.φ₂, φ₁_L₂_f,
    pullback.lift_fst_assoc, w₀₂_τ₂, zero_comp]

