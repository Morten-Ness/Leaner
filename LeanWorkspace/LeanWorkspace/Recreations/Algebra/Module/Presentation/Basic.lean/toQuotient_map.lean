import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

theorem toQuotient_map : relations.toQuotient.comp relations.map = 0 := by aesop

