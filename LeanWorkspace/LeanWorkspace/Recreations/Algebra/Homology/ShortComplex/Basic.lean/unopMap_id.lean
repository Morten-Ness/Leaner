import Mathlib

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

variable (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem unopMap_id (S : CategoryTheory.ShortComplex Cᵒᵖ) : CategoryTheory.ShortComplex.unopMap (𝟙 S) = 𝟙 S.unop := rfl

