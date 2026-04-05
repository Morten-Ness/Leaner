import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem homologyMap'_zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    CategoryTheory.ShortComplex.homologyMap' 0 h₁ h₂ = 0 := CategoryTheory.ShortComplex.HomologyMapData.homologyMap'_eq (HomologyMapData.zero h₁ h₂)

