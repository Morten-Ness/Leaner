import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

theorem ker_toQuotient :
    LinearMap.ker relations.toQuotient = Submodule.span A (Set.range relations.relation) := Submodule.ker_mkQ _

