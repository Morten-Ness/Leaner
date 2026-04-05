import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

theorem cyclesIsoX₂_inv_hom_id (hg : S.g = 0) :
    (S.cyclesIsoX₂ hg).inv ≫ S.iCycles = 𝟙 _ := (S.cyclesIsoX₂ hg).inv_hom_id

