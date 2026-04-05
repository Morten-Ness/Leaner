import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem range_π : LinearMap.range solution.π = Submodule.span A (Set.range solution.var) := Finsupp.range_linearCombination _

