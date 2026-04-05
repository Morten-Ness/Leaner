import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem exact_of_f_is_kernel (hS : IsLimit (KernelFork.ofι S.f S.zero))
    [S.HasHomology] : S.Exact := by
  rw [CategoryTheory.ShortComplex.exact_iff_epi_toCycles]
  have : IsSplitEpi S.toCycles :=
    ⟨⟨{ section_ := hS.lift (KernelFork.ofι S.iCycles S.iCycles_g)
        id := by
          rw [← cancel_mono S.iCycles, assoc, toCycles_i, id_comp]
          exact Fork.IsLimit.lift_ι hS }⟩⟩
  infer_instance

