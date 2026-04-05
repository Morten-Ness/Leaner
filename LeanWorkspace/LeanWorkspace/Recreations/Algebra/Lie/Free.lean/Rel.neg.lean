import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

theorem Rel.neg {a b : lib R X} (h : Rel R X a b) : Rel R X (-a) (-b) := by
  simpa only [neg_one_smul] using h.smul (-1)

