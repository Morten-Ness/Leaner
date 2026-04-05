import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

theorem mem_rootSet_of_mem_rootSpan (I : LieIdeal K L)
    {α : H.root} (hα_span : (α : Dual K H) ∈ I.rootSpan) :
    α ∈ I.rootSet := by
  by_contra hα_not
  have hα_nz := H.isNonZero_coe_root α
  have : I.rootSpan ≤ LinearMap.ker (Dual.eval K H (coroot (α : Weight K H L))) := by
    rw [LieIdeal.rootSpan, Submodule.span_le]
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Dual.eval_apply, rootSystem_root_apply]
    exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hγ hα_not
  have := LinearMap.mem_ker.mp (this hα_span)
  simp only [Dual.eval_apply, Weight.toLinear_apply, root_apply_coroot hα_nz] at this
  exact absurd this two_ne_zero

