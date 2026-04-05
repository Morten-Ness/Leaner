import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

theorem Rel.subRight {a b : lib R X} (c : lib R X) (h : Rel R X a b) : Rel R X (a - c) (b - c) := by
  simpa only [sub_eq_add_neg] using h.add_right (-c)

