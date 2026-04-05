import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

theorem linearEquiv_symm_var (g : relations.G) :
    h.linearEquiv.symm (solution.var g) = relations.toQuotient (Finsupp.single g 1) := h.linearEquiv.injective (by simp)

