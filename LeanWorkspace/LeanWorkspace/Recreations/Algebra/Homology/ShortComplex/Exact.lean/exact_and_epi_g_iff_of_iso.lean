import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_and_epi_g_iff_of_iso (e : S₁ ≅ S₂) :
    S₁.Exact ∧ Epi S₁.g ↔ S₂.Exact ∧ Epi S₂.g := by
  have : Epi S₁.g ↔ Epi S₂.g :=
    (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (CategoryTheory.ShortComplex.π₂.mapIso e) (CategoryTheory.ShortComplex.π₃.mapIso e) e.hom.comm₂₃)
  rw [CategoryTheory.ShortComplex.exact_iff_of_iso e, this]

