import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

theorem cyclesIsoX₂_hom_inv_id (hg : S.g = 0) :
    S.iCycles ≫ (S.cyclesIsoX₂ hg).inv = 𝟙 _ := (S.cyclesIsoX₂ hg).hom_inv_id

