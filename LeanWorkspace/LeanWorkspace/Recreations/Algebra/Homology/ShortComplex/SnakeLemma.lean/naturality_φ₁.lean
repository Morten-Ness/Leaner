import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

variable (S₁ S₂ S₃ : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem naturality_φ₁ (f : S₁ ⟶ S₂) : S₁.φ₁ ≫ f.f₂.τ₁ = CategoryTheory.ShortComplex.SnakeInput.functorP.map f ≫ S₂.φ₁ := by
  simp only [← cancel_mono S₂.L₂.f, assoc, φ₁_L₂_f, ← CategoryTheory.ShortComplex.SnakeInput.naturality_φ₂, f.f₂.comm₁₂, φ₁_L₂_f_assoc]

