import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem homologyMap_zero [S₁.HasHomology] [S₂.HasHomology] :
    CategoryTheory.ShortComplex.homologyMap (0 : S₁ ⟶ S₂) = 0 := CategoryTheory.ShortComplex.homologyMap'_zero _ _

