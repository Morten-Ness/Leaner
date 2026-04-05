import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem hasLeftHomology_iff_unop (S : CategoryTheory.ShortComplex Cᵒᵖ) :
    S.HasLeftHomology ↔ S.unop.HasRightHomology := S.CategoryTheory.ShortComplex.hasRightHomology_iff_op CategoryTheory.ShortComplex.RightHomologyData.unop.symm

