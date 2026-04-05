import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.RightHomologyData) [S.HasRightHomology]

set_option backward.isDefEq.respectTransparency false in
theorem rightHomologyIso_inv_comp_rightHomologyι :
    h.rightHomologyIso.inv ≫ S.rightHomologyι = h.ι ≫ h.opcyclesIso.inv := by
  dsimp only [CategoryTheory.ShortComplex.rightHomologyι, CategoryTheory.ShortComplex.RightHomologyData.rightHomologyIso, CategoryTheory.ShortComplex.RightHomologyData.opcyclesIso, CategoryTheory.ShortComplex.rightHomologyMapIso',
    CategoryTheory.ShortComplex.opcyclesMapIso', Iso.refl]
  rw [CategoryTheory.ShortComplex.rightHomologyι_naturality']

