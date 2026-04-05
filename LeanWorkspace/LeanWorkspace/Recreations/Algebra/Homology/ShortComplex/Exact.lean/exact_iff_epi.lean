import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem exact_iff_epi [HasZeroObject C] (hg : S.g = 0) :
    S.Exact ↔ Epi S.f := by
  constructor
  · intro h
    have := h.hasHomology
    simp only [CategoryTheory.ShortComplex.exact_iff_isZero_homology] at h
    haveI := S.isIso_iCycles hg
    haveI : Epi S.toCycles := epi_of_isZero_cokernel' _ S.homologyIsCokernel h
    rw [← S.toCycles_i]
    apply epi_comp
  · intro
    rw [(HomologyData.ofIsColimitCokernelCofork S hg _
      (CokernelCofork.IsColimit.ofEpiOfIsZero (CokernelCofork.ofπ (0 : S.X₂ ⟶ 0) comp_zero)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

