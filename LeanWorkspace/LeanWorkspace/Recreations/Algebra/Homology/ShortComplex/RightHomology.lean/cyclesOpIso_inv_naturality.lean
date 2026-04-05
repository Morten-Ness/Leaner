import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem cyclesOpIso_inv_naturality (φ : S₁ ⟶ S₂)
    [S₁.HasRightHomology] [S₂.HasRightHomology] :
    (CategoryTheory.ShortComplex.opcyclesMap φ).op ≫ (S₁.cyclesOpIso).inv =
      S₂.cyclesOpIso.inv ≫ cyclesMap (opMap φ) := by
  rw [← cancel_mono S₁.op.iCycles, assoc, assoc, CategoryTheory.ShortComplex.cyclesOpIso_inv_op_iCycles, cyclesMap_i,
    cyclesOpIso_inv_op_iCycles_assoc, ← op_comp, CategoryTheory.ShortComplex.p_opcyclesMap, op_comp, opMap_τ₂]

