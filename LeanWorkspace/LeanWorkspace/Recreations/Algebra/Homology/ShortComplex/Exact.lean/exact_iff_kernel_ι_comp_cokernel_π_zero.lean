import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_iff_kernel_ι_comp_cokernel_π_zero [S.HasHomology]
    [HasKernel S.g] [HasCokernel S.f] :
    S.Exact ↔ kernel.ι S.g ≫ cokernel.π S.f = 0 := by
  haveI := HasLeftHomology.hasCokernel S
  haveI := HasRightHomology.hasKernel S
  exact S.exact_iff_i_p_zero (LeftHomologyData.ofHasKernelOfHasCokernel S)
    (RightHomologyData.ofHasCokernelOfHasKernel S)

