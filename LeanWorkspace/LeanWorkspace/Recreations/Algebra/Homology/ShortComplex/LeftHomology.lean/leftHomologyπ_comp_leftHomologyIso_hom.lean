import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.LeftHomologyData) [S.HasLeftHomology]

set_option backward.isDefEq.respectTransparency false in
theorem leftHomologyπ_comp_leftHomologyIso_hom :
    S.leftHomologyπ ≫ h.leftHomologyIso.hom = h.cyclesIso.hom ≫ h.π := by
  dsimp only [CategoryTheory.ShortComplex.leftHomologyπ, CategoryTheory.ShortComplex.LeftHomologyData.leftHomologyIso, CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso, CategoryTheory.ShortComplex.leftHomologyMapIso',
    CategoryTheory.ShortComplex.cyclesMapIso', Iso.refl]
  rw [← CategoryTheory.ShortComplex.leftHomologyπ_naturality']

