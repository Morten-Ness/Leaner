import Mathlib

variable {R M : Type*}

variable [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

theorem isTorsionFree_iff_torsion_eq_bot : IsTorsionFree R M ↔ torsion R M = ⊥ := by
  simp [torsion, Submodule.torsion', subset_antisymm_iff, exists_ne, isTorsionFree_iff_smul_eq_zero]
  grind

