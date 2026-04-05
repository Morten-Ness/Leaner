import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

theorem map_single (r : relations.R) :
    relations.map (Finsupp.single r 1) = relations.relation r := by
  simp [Module.Relations.map]

