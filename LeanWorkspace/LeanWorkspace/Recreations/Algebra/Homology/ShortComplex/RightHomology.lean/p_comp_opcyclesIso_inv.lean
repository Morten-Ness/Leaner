import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.RightHomologyData) [S.HasRightHomology]

set_option backward.isDefEq.respectTransparency false in
theorem p_comp_opcyclesIso_inv : h.p ≫ h.opcyclesIso.inv = S.pOpcycles := by
  dsimp [CategoryTheory.ShortComplex.pOpcycles, CategoryTheory.ShortComplex.RightHomologyData.opcyclesIso]
  simp only [CategoryTheory.ShortComplex.p_opcyclesMap', id_τ₂, id_comp]

