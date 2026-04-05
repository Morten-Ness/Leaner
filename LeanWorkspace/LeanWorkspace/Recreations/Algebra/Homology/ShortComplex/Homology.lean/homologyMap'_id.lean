import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem homologyMap'_id (h : S.HomologyData) :
    CategoryTheory.ShortComplex.homologyMap' (𝟙 S) h h = 𝟙 _ := CategoryTheory.ShortComplex.HomologyMapData.homologyMap'_eq (HomologyMapData.id h)

