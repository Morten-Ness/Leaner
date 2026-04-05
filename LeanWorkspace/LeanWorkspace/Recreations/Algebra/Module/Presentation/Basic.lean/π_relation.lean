import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem π_relation (r : relations.R) : solution.π (relations.relation r) = 0 := solution.linearCombination_var_relation r

