import Mathlib

variable {A : Type u} [Ring A] (relations : Relations.{w₀, w₁} A)
  (M : Type v) [AddCommGroup M] [Module A M]

variable [IsEmpty relations.R]

theorem solutionFinsupp_isPresentation :
    relations.solutionFinsupp.IsPresentation := (Module.Relations.solutionFinsupp.isPresentationCore relations).isPresentation

