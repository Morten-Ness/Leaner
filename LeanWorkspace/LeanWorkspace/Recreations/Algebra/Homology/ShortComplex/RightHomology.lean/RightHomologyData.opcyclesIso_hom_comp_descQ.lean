import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : RightHomologyData S) {A : C}
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [HasRightHomology S]

theorem RightHomologyData.opcyclesIso_hom_comp_descQ :
    h.opcyclesIso.hom ≫ h.descQ k hk = S.descOpcycles k hk := by
  rw [← h.opcyclesIso_inv_comp_descOpcycles, Iso.hom_inv_id_assoc]

