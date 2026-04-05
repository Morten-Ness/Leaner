import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem cyclesOpIso_hom_naturality (φ : S₁ ⟶ S₂)
    [S₁.HasRightHomology] [S₂.HasRightHomology] :
    cyclesMap (opMap φ) ≫ (S₁.cyclesOpIso).hom =
      S₂.cyclesOpIso.hom ≫ (CategoryTheory.ShortComplex.opcyclesMap φ).op := by
  rw [← cancel_mono (S₁.cyclesOpIso).inv, assoc, assoc, Iso.hom_inv_id, comp_id,
    CategoryTheory.ShortComplex.cyclesOpIso_inv_naturality, Iso.hom_inv_id_assoc]

