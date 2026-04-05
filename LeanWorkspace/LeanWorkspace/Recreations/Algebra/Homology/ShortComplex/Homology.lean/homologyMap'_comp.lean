import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem homologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) (h₃ : S₃.HomologyData) :
    CategoryTheory.ShortComplex.homologyMap' (φ₁ ≫ φ₂) h₁ h₃ = CategoryTheory.ShortComplex.homologyMap' φ₁ h₁ h₂ ≫
      CategoryTheory.ShortComplex.homologyMap' φ₂ h₂ h₃ := leftHomologyMap'_comp _ _ _ _ _

