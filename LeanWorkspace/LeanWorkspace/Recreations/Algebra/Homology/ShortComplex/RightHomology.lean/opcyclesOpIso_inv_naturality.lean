import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem opcyclesOpIso_inv_naturality (φ : S₁ ⟶ S₂)
    [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    (cyclesMap φ).op ≫ (S₁.opcyclesOpIso).inv =
      S₂.opcyclesOpIso.inv ≫ CategoryTheory.ShortComplex.opcyclesMap (opMap φ) := by
  rw [← cancel_epi (S₂.opcyclesOpIso.hom), Iso.hom_inv_id_assoc,
    ← opcyclesOpIso_hom_naturality_assoc, Iso.hom_inv_id, comp_id]

