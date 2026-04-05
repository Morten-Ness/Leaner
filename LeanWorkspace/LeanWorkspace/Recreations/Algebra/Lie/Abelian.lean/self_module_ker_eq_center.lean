import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

theorem self_module_ker_eq_center : LieModule.ker R L L = center R L := by
  ext y
  simp only [LieModule.mem_maxTrivSubmodule, LieModule.mem_ker, ← lie_skew _ y, neg_eq_zero]

