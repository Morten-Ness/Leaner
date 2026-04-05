import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

theorem rootSet_apply_coroot_eq_zero_of_notMem_rootSet (I : LieIdeal K L)
    {α : H.root} (hα : α ∈ I.rootSet)
    {β : H.root} (hβ : β ∉ I.rootSet) :
    (α : Weight K H L) (coroot β) = 0 := by
  have h_ker : coroot (α : Weight K H L) ∈ (β : Weight K H L).ker :=
    I.root_apply_eq_zero_of_notMem_rootSet
      (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule _)) hβ
  change coroot (β : Weight K H L) ∈ (α : Weight K H L).ker
  rw [← orthogonal_span_coroot_eq_ker,
    LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker, LinearMap.mem_ker]
  exact traceForm_eq_zero_of_mem_ker_of_mem_span_coroot h_ker (Submodule.mem_span_singleton_self _)

