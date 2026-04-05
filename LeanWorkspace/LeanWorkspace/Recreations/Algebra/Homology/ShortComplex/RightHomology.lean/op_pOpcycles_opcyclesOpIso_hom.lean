import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem op_pOpcycles_opcyclesOpIso_hom [S.HasLeftHomology] :
    S.op.pOpcycles ≫ S.opcyclesOpIso.hom = S.iCycles.op := by
  dsimp [CategoryTheory.ShortComplex.opcyclesOpIso]
  rw [← S.CategoryTheory.ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv leftHomologyData.op, assoc,
    Iso.inv_hom_id, comp_id]
  rfl

