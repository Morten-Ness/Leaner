import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem cyclesMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    CategoryTheory.ShortComplex.cyclesMap (φ₁ ≫ φ₂) = CategoryTheory.ShortComplex.cyclesMap φ₁ ≫ CategoryTheory.ShortComplex.cyclesMap φ₂ := CategoryTheory.ShortComplex.cyclesMap'_comp _ _ _ _ _

attribute [simp] CategoryTheory.ShortComplex.leftHomologyMap_comp cyclesMap_comp

