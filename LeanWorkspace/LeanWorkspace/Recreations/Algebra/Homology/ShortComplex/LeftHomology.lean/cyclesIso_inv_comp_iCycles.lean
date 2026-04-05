import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.LeftHomologyData) [S.HasLeftHomology]

theorem cyclesIso_inv_comp_iCycles : h.cyclesIso.inv ≫ S.iCycles = h.i := by
  simp only [← CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i h, Iso.inv_hom_id_assoc]

