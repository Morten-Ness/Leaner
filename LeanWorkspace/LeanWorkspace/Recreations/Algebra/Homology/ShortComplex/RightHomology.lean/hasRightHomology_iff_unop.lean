import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem hasRightHomology_iff_unop (S : CategoryTheory.ShortComplex Cᵒᵖ) :
    S.HasRightHomology ↔ S.unop.HasLeftHomology := S.CategoryTheory.ShortComplex.hasLeftHomology_iff_op CategoryTheory.ShortComplex.RightHomologyData.unop.symm

