import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem exact_iff_epi_kernel_lift [S.HasHomology] [HasKernel S.g] :
    S.Exact ↔ Epi (kernel.lift S.g S.f S.zero) := by
  rw [CategoryTheory.ShortComplex.exact_iff_epi_toCycles]
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) S.cyclesIsoKernel (by cat_disch)

