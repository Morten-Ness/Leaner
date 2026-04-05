import Mathlib

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

variable (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem isIso_of_isIso (f : S₁ ⟶ S₂) [IsIso f.τ₁] [IsIso f.τ₂] [IsIso f.τ₃] : IsIso f := (CategoryTheory.ShortComplex.isoMk (asIso f.τ₁) (asIso f.τ₂) (asIso f.τ₃)).isIso_hom

