import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem hasRightHomology_of_iso {S₁ S₂ : CategoryTheory.ShortComplex C}
    (e : S₁ ≅ S₂) [HasRightHomology S₁] : HasRightHomology S₂ := CategoryTheory.ShortComplex.hasRightHomology_of_epi_of_isIso_of_mono e.hom

