import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem lift_φ₂ {A : C} (a : A ⟶ S.L₁.X₂) (b : A ⟶ S.L₀.X₃) (h : a ≫ S.L₁.g = b ≫ S.v₀₁.τ₃) :
    pullback.lift a b h ≫ S.φ₂ = a ≫ S.v₁₂.τ₂ := by
  simp [CategoryTheory.ShortComplex.SnakeInput.φ₂]

