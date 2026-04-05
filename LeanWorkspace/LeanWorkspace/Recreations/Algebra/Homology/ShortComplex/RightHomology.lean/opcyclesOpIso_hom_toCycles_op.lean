import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem opcyclesOpIso_hom_toCycles_op [S.HasLeftHomology] :
    S.opcyclesOpIso.hom ≫ S.toCycles.op = S.op.fromOpcycles := by
  dsimp [CategoryTheory.ShortComplex.opcyclesOpIso, toCycles]
  rw [← cancel_epi S.op.pOpcycles, CategoryTheory.ShortComplex.p_fromOpcycles,
    RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc,
    LeftHomologyData.op_p, ← op_comp, LeftHomologyData.f'_i, op_g]

