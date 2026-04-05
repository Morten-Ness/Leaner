import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasRightHomology]

theorem opcyclesIsoX₂_hom_inv_id (hf : S.f = 0) :
    (S.opcyclesIsoX₂ hf).hom ≫ S.pOpcycles = 𝟙 _ := (S.opcyclesIsoX₂ hf).hom_inv_id

