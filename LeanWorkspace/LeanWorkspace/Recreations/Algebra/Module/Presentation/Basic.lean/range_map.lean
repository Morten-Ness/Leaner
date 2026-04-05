import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

theorem range_map :
    LinearMap.range relations.map = Submodule.span A (Set.range relations.relation) := Finsupp.range_linearCombination _

