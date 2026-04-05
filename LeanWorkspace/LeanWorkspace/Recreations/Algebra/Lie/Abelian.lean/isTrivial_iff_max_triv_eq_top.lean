import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

theorem isTrivial_iff_max_triv_eq_top : IsTrivial L M ↔ LieModule.maxTrivSubmodule R L M = ⊤ := by
  constructor
  · rintro ⟨h⟩; ext; simp only [LieModule.mem_maxTrivSubmodule, h, forall_const, LieSubmodule.mem_top]
  · intro h; constructor; intro x m; revert x
    rw [← LieModule.mem_maxTrivSubmodule R L M, h]; exact LieSubmodule.mem_top m

