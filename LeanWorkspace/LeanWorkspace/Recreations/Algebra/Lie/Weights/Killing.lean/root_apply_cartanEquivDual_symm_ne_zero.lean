import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem root_apply_cartanEquivDual_symm_ne_zero {α : Weight K H L} (hα : α.IsNonZero) :
    α ((LieAlgebra.IsKilling.cartanEquivDual H).symm α) ≠ 0 := by
  contrapose! hα
  suffices (LieAlgebra.IsKilling.cartanEquivDual H).symm α ∈ α.ker ⊓ corootSpace α by
    rw [(LieAlgebra.IsKilling.disjoint_ker_weight_corootSpace α).eq_bot] at this
    simpa using this
  exact Submodule.mem_inf.mp ⟨hα, LieAlgebra.IsKilling.cartanEquivDual_symm_apply_mem_corootSpace α⟩

