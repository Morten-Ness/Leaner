import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.RightHomologyData) [S.HasRightHomology]

theorem pOpcycles_comp_opcyclesIso_hom : S.pOpcycles ≫ h.opcyclesIso.hom = h.p := by
  simp only [← CategoryTheory.ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv h, assoc, Iso.inv_hom_id, comp_id]

