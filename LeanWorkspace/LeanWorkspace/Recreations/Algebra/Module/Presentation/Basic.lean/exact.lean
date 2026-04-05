import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

theorem exact : Function.Exact relations.map solution.π := by
  rw [LinearMap.exact_iff, Module.Relations.range_map, ← Module.Relations.Solution.injective_fromQuotient_iff_ker_π_eq_span solution]
  exact h.bijective.1

