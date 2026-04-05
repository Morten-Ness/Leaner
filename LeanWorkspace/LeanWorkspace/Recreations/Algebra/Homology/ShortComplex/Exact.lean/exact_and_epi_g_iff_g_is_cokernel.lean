import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem exact_and_epi_g_iff_g_is_cokernel [S.HasHomology] :
    S.Exact ∧ Epi S.g ↔ Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero)) := by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.gIsCokernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_g_is_cokernel hS, epi_of_isColimit_cofork hS⟩

