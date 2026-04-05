import Mathlib

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

variable (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem opMap_id : CategoryTheory.ShortComplex.opMap (𝟙 S) = 𝟙 S.op := rfl

