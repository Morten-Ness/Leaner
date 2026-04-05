import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

theorem linearEquiv_apply (x : relations.Quotient) :
    h.linearEquiv x = solution.fromQuotient x := rfl

