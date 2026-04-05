import Mathlib

variable (A : Type u) [Ring A] (M : Type v) [AddCommGroup M] [Module A M]

theorem tautologicalSolution_isPresentation :
    (Module.Presentation.tautologicalSolution A M).IsPresentation := (Module.Presentation.tautologicalSolutionIsPresentationCore A M).isPresentation

