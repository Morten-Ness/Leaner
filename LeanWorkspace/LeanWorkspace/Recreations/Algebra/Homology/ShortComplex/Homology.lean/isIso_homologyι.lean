import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {C} {A : C}

theorem isIso_homologyι (hg : S.g = 0) [S.HasHomology] :
    IsIso S.homologyι := by
  have := S.isIso_rightHomologyι hg
  dsimp only [CategoryTheory.ShortComplex.homologyι]
  infer_instance

