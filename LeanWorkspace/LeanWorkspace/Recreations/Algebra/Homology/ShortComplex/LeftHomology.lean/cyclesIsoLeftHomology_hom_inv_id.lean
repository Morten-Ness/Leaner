import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

theorem cyclesIsoLeftHomology_hom_inv_id (hf : S.f = 0) :
    S.leftHomologyπ ≫ (S.cyclesIsoLeftHomology hf).inv = 𝟙 _ := (S.cyclesIsoLeftHomology hf).hom_inv_id

