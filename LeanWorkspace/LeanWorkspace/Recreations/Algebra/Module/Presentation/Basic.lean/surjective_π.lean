import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

theorem surjective_π : Function.Surjective solution.π := by
  simpa only [← Module.Relations.Solution.surjective_fromQuotient_iff_surjective_π] using h.bijective.2

