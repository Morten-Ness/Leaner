import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem add_eq_iff {x y z : Tropical R} : x + y = z ↔ x = z ∧ x ≤ y ∨ y = z ∧ y ≤ x := by
  rw [Tropical.trop_add_def, Tropical.trop_eq_iff_eq_untrop]
  simp [min_eq_iff]

