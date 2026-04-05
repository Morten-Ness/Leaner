import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

theorem cyclesIsoLeftHomology_inv_hom_id (hf : S.f = 0) :
    (S.cyclesIsoLeftHomology hf).inv ≫ S.leftHomologyπ = 𝟙 _ := (S.cyclesIsoLeftHomology hf).inv_hom_id

