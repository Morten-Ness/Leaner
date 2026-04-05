import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

variable (S₁ S₂ S₃ : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem naturality_φ₂ (f : S₁ ⟶ S₂) : S₁.φ₂ ≫ f.f₂.τ₂ = CategoryTheory.ShortComplex.SnakeInput.functorP.map f ≫ S₂.φ₂ := by
  dsimp [CategoryTheory.ShortComplex.SnakeInput.φ₂]
  simp only [assoc, pullback.lift_fst_assoc, ← comp_τ₂, f.comm₁₂]

