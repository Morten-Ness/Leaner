import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem add_eq_left_iff {x y : Tropical R} : x + y = x ↔ x ≤ y := by
  rw [Tropical.trop_add_def, Tropical.trop_eq_iff_eq_untrop, ← Tropical.untrop_le_iff, min_eq_left_iff]

