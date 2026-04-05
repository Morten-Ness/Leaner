import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem isPresentation_mk
    (h₁ : Submodule.span A (Set.range solution.var) = ⊤)
    (h₂ : LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation)) :
    solution.IsPresentation := by
  rw [Module.Relations.Solution.isPresentation_iff]; constructor <;> assumption

