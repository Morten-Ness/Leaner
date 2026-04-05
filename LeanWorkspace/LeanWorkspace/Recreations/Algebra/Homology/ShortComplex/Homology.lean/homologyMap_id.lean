import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem homologyMap_id [HasHomology S] :
    CategoryTheory.ShortComplex.homologyMap (𝟙 S) = 𝟙 _ := CategoryTheory.ShortComplex.homologyMap'_id _

