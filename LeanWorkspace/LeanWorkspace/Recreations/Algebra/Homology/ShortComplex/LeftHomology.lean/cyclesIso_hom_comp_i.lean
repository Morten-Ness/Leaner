import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.LeftHomologyData) [S.HasLeftHomology]

set_option backward.isDefEq.respectTransparency false in
theorem cyclesIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles := by
  dsimp [CategoryTheory.ShortComplex.iCycles, CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso]
  simp only [CategoryTheory.ShortComplex.cyclesMap'_i, id_τ₂, comp_id]

