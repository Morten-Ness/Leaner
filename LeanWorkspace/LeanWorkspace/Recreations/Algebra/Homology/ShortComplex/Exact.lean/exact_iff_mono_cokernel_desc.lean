import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem exact_iff_mono_cokernel_desc [S.HasHomology] [HasCokernel S.f] :
    S.Exact ↔ Mono (cokernel.desc S.f S.g S.zero) := by
  rw [CategoryTheory.ShortComplex.exact_iff_mono_fromOpcycles]
  refine (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (Iso.symm ?_)
  exact Arrow.isoMk S.opcyclesIsoCokernel.symm (Iso.refl _) (by cat_disch)

