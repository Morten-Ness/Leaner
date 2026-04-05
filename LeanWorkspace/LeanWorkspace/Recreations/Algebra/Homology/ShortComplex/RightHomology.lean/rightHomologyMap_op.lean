import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem rightHomologyMap_op (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    (CategoryTheory.ShortComplex.rightHomologyMap φ).op = S₂.leftHomologyOpIso.inv ≫ leftHomologyMap (opMap φ) ≫
      S₁.leftHomologyOpIso.hom := by
  dsimp [CategoryTheory.ShortComplex.leftHomologyOpIso, LeftHomologyData.leftHomologyIso, leftHomologyMap,
    CategoryTheory.ShortComplex.rightHomologyMap]
  simp only [← leftHomologyMap'_comp, comp_id, id_comp, CategoryTheory.ShortComplex.rightHomologyMap'_op]

