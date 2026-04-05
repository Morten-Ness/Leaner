import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem homologyMap_comp [HasHomology S₁] [HasHomology S₂] [HasHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    CategoryTheory.ShortComplex.homologyMap (φ₁ ≫ φ₂) = CategoryTheory.ShortComplex.homologyMap φ₁ ≫ CategoryTheory.ShortComplex.homologyMap φ₂ := CategoryTheory.ShortComplex.homologyMap'_comp _ _ _ _ _

