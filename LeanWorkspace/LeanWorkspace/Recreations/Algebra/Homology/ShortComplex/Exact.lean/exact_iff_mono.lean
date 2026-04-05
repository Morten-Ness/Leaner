import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem exact_iff_mono [HasZeroObject C] (hf : S.f = 0) :
    S.Exact ↔ Mono S.g := by
  constructor
  · intro h
    have := h.hasHomology
    simp only [CategoryTheory.ShortComplex.exact_iff_isZero_homology] at h
    have := S.isIso_pOpcycles hf
    have := mono_of_isZero_kernel' _ S.homologyIsKernel h
    rw [← S.p_fromOpcycles]
    apply mono_comp
  · intro
    rw [(HomologyData.ofIsLimitKernelFork S hf _
      (KernelFork.IsLimit.ofMonoOfIsZero (KernelFork.ofι (0 : 0 ⟶ S.X₂) zero_comp)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

