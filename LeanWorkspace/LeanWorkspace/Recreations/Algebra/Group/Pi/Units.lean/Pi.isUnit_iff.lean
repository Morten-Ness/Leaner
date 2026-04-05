import Mathlib

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {x : Π i, M i}

theorem Pi.isUnit_iff :
    IsUnit x ↔ ∀ i, IsUnit (x i) := by
  simp_rw [isUnit_iff_exists, funext_iff, ← forall_and]
  exact Classical.skolem (p := fun i y ↦ x i * y = 1 ∧ y * x i = 1).symm

