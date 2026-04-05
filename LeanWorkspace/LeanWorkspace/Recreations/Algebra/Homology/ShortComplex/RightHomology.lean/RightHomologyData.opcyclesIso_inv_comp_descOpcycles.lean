import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : RightHomologyData S) {A : C}
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [HasRightHomology S]

theorem RightHomologyData.opcyclesIso_inv_comp_descOpcycles :
    h.opcyclesIso.inv ≫ S.descOpcycles k hk = h.descQ k hk := by
  simp only [← cancel_epi h.p, p_comp_opcyclesIso_inv_assoc, CategoryTheory.ShortComplex.p_descOpcycles, CategoryTheory.ShortComplex.RightHomologyData.p_descQ]

