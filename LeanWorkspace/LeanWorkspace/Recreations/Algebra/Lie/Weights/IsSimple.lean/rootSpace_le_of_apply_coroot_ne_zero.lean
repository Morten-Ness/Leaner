import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

theorem rootSpace_le_of_apply_coroot_ne_zero (I : LieIdeal K L)
    {α : Weight K H L} (hα : rootSpace H α ≤ I.restr H)
    {γ : H → K} (hγ_ne : γ (coroot α) ≠ 0) :
    rootSpace H γ ≤ I.restr H := by
  intro y hy
  have : γ (coroot α) • y ∈ I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy (coroot α)]
    exact lie_mem_left K L I _ y
      (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule α))
  exact I.toSubmodule.smul_mem_iff hγ_ne |>.mp this

