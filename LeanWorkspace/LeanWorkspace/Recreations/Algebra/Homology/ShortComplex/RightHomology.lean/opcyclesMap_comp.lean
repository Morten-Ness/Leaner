import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem opcyclesMap_comp [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    CategoryTheory.ShortComplex.opcyclesMap (φ₁ ≫ φ₂) = CategoryTheory.ShortComplex.opcyclesMap φ₁ ≫ CategoryTheory.ShortComplex.opcyclesMap φ₂ := CategoryTheory.ShortComplex.opcyclesMap'_comp _ _ _ _ _

attribute [simp] CategoryTheory.ShortComplex.rightHomologyMap_comp opcyclesMap_comp

