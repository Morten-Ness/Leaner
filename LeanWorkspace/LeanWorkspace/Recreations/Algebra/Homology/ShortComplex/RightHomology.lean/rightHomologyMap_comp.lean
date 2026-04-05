import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem rightHomologyMap_comp [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    CategoryTheory.ShortComplex.rightHomologyMap (φ₁ ≫ φ₂) = CategoryTheory.ShortComplex.rightHomologyMap φ₁ ≫ CategoryTheory.ShortComplex.rightHomologyMap φ₂ := CategoryTheory.ShortComplex.rightHomologyMap'_comp _ _ _ _ _

