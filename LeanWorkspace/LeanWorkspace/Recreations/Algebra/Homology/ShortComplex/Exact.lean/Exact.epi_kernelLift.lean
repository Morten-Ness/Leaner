import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.epi_kernelLift [S.HasHomology] [HasKernel S.g] (hS : S.Exact) :
    Epi (Limits.kernel.lift S.g S.f S.zero) := S.exact_iff_epi_kernel_lift.1 hS

