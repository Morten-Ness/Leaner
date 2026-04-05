import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

theorem surjective_toQuotient : Function.Surjective relations.toQuotient := Submodule.mkQ_surjective _

