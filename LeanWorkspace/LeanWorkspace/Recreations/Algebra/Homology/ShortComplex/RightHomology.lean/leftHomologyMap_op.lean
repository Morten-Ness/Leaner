import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem leftHomologyMap_op (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    (leftHomologyMap φ).op = S₂.rightHomologyOpIso.inv ≫ CategoryTheory.ShortComplex.rightHomologyMap (opMap φ) ≫
      S₁.rightHomologyOpIso.hom := by
  dsimp [CategoryTheory.ShortComplex.rightHomologyOpIso, RightHomologyData.rightHomologyIso, CategoryTheory.ShortComplex.rightHomologyMap,
    leftHomologyMap]
  simp only [← CategoryTheory.ShortComplex.rightHomologyMap'_comp, comp_id, id_comp, CategoryTheory.ShortComplex.leftHomologyMap'_op]

