import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasRightHomology]

theorem opcyclesIsoRightHomology_inv_hom_id (hg : S.g = 0) :
    S.rightHomologyι ≫ (S.opcyclesIsoRightHomology hg).hom = 𝟙 _ := (S.opcyclesIsoRightHomology hg).inv_hom_id

