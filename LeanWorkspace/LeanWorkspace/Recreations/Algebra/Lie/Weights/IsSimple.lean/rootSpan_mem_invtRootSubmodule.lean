import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

theorem rootSpan_mem_invtRootSubmodule (I : LieIdeal K L) :
    I.rootSpan ∈ (rootSystem H).invtRootSubmodule := by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro β
  rw [Module.End.mem_invtSubmodule, LieIdeal.rootSpan, Submodule.span_le]
  rintro - ⟨α, hα, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, ← RootPairing.root_reflectionPerm]
  exact Submodule.subset_span ⟨_, (I.reflectionPerm_mem_rootSet_iff α β).mpr hα, rfl⟩

