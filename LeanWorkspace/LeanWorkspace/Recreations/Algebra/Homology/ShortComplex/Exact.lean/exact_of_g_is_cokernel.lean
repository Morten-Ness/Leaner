import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem exact_of_g_is_cokernel (hS : IsColimit (CokernelCofork.ofπ S.g S.zero))
    [S.HasHomology] : S.Exact := by
  rw [CategoryTheory.ShortComplex.exact_iff_mono_fromOpcycles]
  have : IsSplitMono S.fromOpcycles :=
    ⟨⟨{ retraction := hS.desc (CokernelCofork.ofπ S.pOpcycles S.f_pOpcycles)
        id := by
          rw [← cancel_epi S.pOpcycles, p_fromOpcycles_assoc, comp_id]
          exact Cofork.IsColimit.π_desc hS }⟩⟩
  infer_instance

