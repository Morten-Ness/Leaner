import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem cyclesOpIso_inv_op_iCycles [S.HasRightHomology] :
    S.cyclesOpIso.inv ≫ S.op.iCycles = S.pOpcycles.op := by
  dsimp [CategoryTheory.ShortComplex.cyclesOpIso]
  rw [← S.rightHomologyData.op.cyclesIso_hom_comp_i, Iso.inv_hom_id_assoc]
  rfl

