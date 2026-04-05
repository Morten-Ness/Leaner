import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem isIso_opcyclesMap_of_isIso_of_epi' (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₁ : Epi φ.τ₁)
    [S₁.HasRightHomology] [S₂.HasRightHomology] :
    IsIso (CategoryTheory.ShortComplex.opcyclesMap φ) := CategoryTheory.ShortComplex.isIso_opcyclesMap'_of_isIso_of_epi φ h₂ h₁ _ _

