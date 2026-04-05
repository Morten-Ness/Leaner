import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

set_option backward.isDefEq.respectTransparency false in
theorem leftRightHomologyComparison'_fac (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [S.HasHomology] :
    CategoryTheory.ShortComplex.leftRightHomologyComparison' h₁ h₂ = h₁.homologyIso.inv ≫ h₂.homologyIso.hom := by
  rw [CategoryTheory.ShortComplex.leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'
    S.homologyData h₁ h₂]
  dsimp only [CategoryTheory.ShortComplex.LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl, leftHomologyMapIso', CategoryTheory.ShortComplex.leftHomologyIso,
    CategoryTheory.ShortComplex.RightHomologyData.homologyIso, RightHomologyData.rightHomologyIso,
    rightHomologyMapIso', CategoryTheory.ShortComplex.rightHomologyIso]
  simp only [assoc, ← leftHomologyMap'_comp_assoc, id_comp, ← rightHomologyMap'_comp]

