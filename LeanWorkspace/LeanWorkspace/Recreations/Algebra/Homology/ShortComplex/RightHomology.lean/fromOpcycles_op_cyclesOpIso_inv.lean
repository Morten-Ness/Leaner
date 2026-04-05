import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem fromOpcycles_op_cyclesOpIso_inv [S.HasRightHomology] :
    S.fromOpcycles.op ≫ S.cyclesOpIso.inv = S.op.toCycles := by
  dsimp [CategoryTheory.ShortComplex.cyclesOpIso, CategoryTheory.ShortComplex.fromOpcycles]
  rw [← cancel_mono S.op.iCycles, assoc, toCycles_i,
    LeftHomologyData.cyclesIso_inv_comp_iCycles, RightHomologyData.op_i,
    ← op_comp, RightHomologyData.p_g', op_f]

