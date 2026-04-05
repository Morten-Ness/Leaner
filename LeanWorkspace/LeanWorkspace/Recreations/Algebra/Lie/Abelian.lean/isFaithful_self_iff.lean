import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

theorem isFaithful_self_iff : LieModule.IsFaithful R L L ↔ center R L = ⊥ := by
  rw [LieModule.isFaithful_iff_ker_eq_bot, LieAlgebra.self_module_ker_eq_center]

