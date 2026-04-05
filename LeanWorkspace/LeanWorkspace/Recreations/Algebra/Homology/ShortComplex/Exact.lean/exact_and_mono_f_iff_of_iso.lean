import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_and_mono_f_iff_of_iso (e : S₁ ≅ S₂) :
    S₁.Exact ∧ Mono S₁.f ↔ S₂.Exact ∧ Mono S₂.f := by
  have : Mono S₁.f ↔ Mono S₂.f :=
    (MorphismProperty.monomorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (CategoryTheory.ShortComplex.π₁.mapIso e) (CategoryTheory.ShortComplex.π₂.mapIso e) e.hom.comm₁₂)
  rw [CategoryTheory.ShortComplex.exact_iff_of_iso e, this]

