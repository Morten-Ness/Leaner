import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_iff_homology_iso_zero [S.HasHomology] [HasZeroObject C] :
    S.Exact ↔ Nonempty (S.homology ≅ 0) := by
  rw [CategoryTheory.ShortComplex.exact_iff_isZero_homology]
  constructor
  · intro h
    exact ⟨h.isoZero⟩
  · rintro ⟨e⟩
    exact IsZero.of_iso (isZero_zero C) e

