import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem isTorsionBy_iff_torsionBy_eq_top : IsTorsionBy R M a ↔ Submodule.torsionBy R M a = ⊤ := by
  rw [← Submodule.torsionBySet_singleton_eq, ← Module.isTorsionBySet_singleton_iff,
    Module.isTorsionBySet_iff_torsionBySet_eq_top]

