import Mathlib

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

variable (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem π₁Toπ₂_comp_π₂Toπ₃ : (π₁Toπ₂ : (_ : _ ⥤ C) ⟶ _) ≫ π₂Toπ₃ = 0 := by cat_disch

