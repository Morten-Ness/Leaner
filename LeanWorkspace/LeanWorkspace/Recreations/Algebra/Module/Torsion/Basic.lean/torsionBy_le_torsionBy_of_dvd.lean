import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBy_le_torsionBy_of_dvd (a b : R) (dvd : a ∣ b) :
    Submodule.torsionBy R M a ≤ Submodule.torsionBy R M b := by
  rw [← Submodule.torsionBySet_span_singleton_eq, ← Submodule.torsionBySet_singleton_eq]
  apply Submodule.torsionBySet_le_torsionBySet_of_subset
  rintro c (rfl : c = b); exact Ideal.mem_span_singleton.mpr dvd

