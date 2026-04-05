import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {C} {A : C}

theorem isIso_homologyπ (hf : S.f = 0) [S.HasHomology] :
    IsIso S.homologyπ := by
  have := S.isIso_leftHomologyπ hf
  dsimp only [CategoryTheory.ShortComplex.homologyπ]
  infer_instance

