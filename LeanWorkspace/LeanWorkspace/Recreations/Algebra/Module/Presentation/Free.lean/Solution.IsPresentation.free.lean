import Mathlib

variable {A : Type u} [Ring A] (relations : Relations.{w₀, w₁} A)
  (M : Type v) [AddCommGroup M] [Module A M]

variable [IsEmpty relations.R]

theorem Solution.IsPresentation.free {solution : relations.Solution M}
    (h : solution.IsPresentation) :
    Module.Free A M := Free.of_equiv ((Module.Relations.solutionFinsupp_isPresentation relations).uniq h)

