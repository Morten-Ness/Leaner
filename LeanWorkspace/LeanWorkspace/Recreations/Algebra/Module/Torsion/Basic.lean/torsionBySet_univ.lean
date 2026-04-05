import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_univ : Submodule.torsionBySet R M Set.univ = ⊥ := by
  rw [eq_bot_iff, ← Submodule.torsionBy_one, ← Submodule.torsionBySet_singleton_eq]
  exact Submodule.torsionBySet_le_torsionBySet_of_subset fun _ _ => trivial

