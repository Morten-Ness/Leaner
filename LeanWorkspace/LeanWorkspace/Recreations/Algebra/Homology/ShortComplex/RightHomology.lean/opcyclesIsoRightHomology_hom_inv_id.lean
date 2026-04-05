import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasRightHomology]

theorem opcyclesIsoRightHomology_hom_inv_id (hg : S.g = 0) :
    (S.opcyclesIsoRightHomology hg).hom ≫ S.rightHomologyι = 𝟙 _ := (S.opcyclesIsoRightHomology hg).hom_inv_id

