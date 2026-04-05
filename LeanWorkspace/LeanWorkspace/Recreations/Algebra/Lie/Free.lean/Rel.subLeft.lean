import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

theorem Rel.subLeft (a : lib R X) {b c : lib R X} (h : Rel R X b c) : Rel R X (a - b) (a - c) := by
  simpa only [sub_eq_add_neg] using h.neg.addLeft a

