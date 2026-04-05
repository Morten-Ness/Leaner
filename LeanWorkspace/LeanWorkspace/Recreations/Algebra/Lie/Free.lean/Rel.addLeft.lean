import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

theorem Rel.addLeft (a : lib R X) {b c : lib R X} (h : Rel R X b c) : Rel R X (a + b) (a + c) := by
  rw [add_comm _ b, add_comm _ c]; exact h.add_right _

