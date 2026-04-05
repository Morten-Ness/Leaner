import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [Module.Free R M] [Module.Finite R M]

variable [IsDomain R] [IsPrincipalIdealRing R]
  (N : LieSubmodule R L M) (I : LieIdeal R L) (h : I ≤ N.idealizer) (x : L) {y : L} (hy : y ∈ I)

include h hy in
theorem traceForm_eq_zero_of_isTrivial [LieModule.IsTrivial I N] :
    trace R M (φ x ∘ₗ φ y) = 0 := by
  let hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)
  suffices (φ x ∘ₗ φ y).restrict hy' = 0 by
    simp [this, N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  ext (n : N)
  suffices ⁅y, (n : M)⁆ = 0 by simp [this]
  exact Submodule.coe_eq_zero.mpr (LieModule.IsTrivial.trivial (⟨y, hy⟩ : I) n)

