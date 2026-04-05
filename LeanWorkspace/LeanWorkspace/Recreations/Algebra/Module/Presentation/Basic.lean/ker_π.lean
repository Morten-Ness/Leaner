import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

theorem ker_π : LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation) := by
  simpa only [← Module.Relations.Solution.injective_fromQuotient_iff_ker_π_eq_span] using h.bijective.1

