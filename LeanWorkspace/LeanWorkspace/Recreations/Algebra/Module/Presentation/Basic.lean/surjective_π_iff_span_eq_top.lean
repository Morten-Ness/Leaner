import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem surjective_π_iff_span_eq_top :
    Function.Surjective solution.π ↔
      Submodule.span A (Set.range solution.var) = ⊤ := by
  rw [← LinearMap.range_eq_top, Module.Relations.Solution.range_π]

