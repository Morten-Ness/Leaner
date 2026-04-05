import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem leftHomologyMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    CategoryTheory.ShortComplex.leftHomologyMap (φ₁ ≫ φ₂) = CategoryTheory.ShortComplex.leftHomologyMap φ₁ ≫ CategoryTheory.ShortComplex.leftHomologyMap φ₂ := CategoryTheory.ShortComplex.leftHomologyMap'_comp _ _ _ _ _

