import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

theorem root_apply_eq_zero_of_notMem_rootSet (I : LieIdeal K L)
    {h : H} (hI : (h : L) ∈ I) {β : H.root} (hβ : β ∉ I.rootSet) :
    (β : Weight K H L) h = 0 := by
  simp only [LieIdeal.mem_rootSet] at hβ
  contrapose! hβ
  intro y hy
  have h_smul : (β : Weight K H L) h • y ∈ I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy h]
    exact lie_mem_left K L I h y hI
  rwa [I.toSubmodule.smul_mem_iff hβ] at h_smul

