import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasRightHomology]

theorem opcyclesIsoX₂_inv_hom_id (hf : S.f = 0) :
    S.pOpcycles ≫ (S.opcyclesIsoX₂ hf).hom = 𝟙 _ := (S.opcyclesIsoX₂ hf).inv_hom_id

