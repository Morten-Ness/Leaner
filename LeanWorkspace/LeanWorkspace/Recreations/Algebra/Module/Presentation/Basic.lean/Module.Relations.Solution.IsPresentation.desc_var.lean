import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

variable {N : Type v'} [AddCommGroup N] [Module A N]

theorem desc_var (s : relations.Solution N) (g : relations.G) :
    h.desc s (solution.var g) = s.var g := by
  dsimp [Module.Relations.Solution.IsPresentation.desc]
  simp only [Module.Relations.Solution.IsPresentation.linearEquiv_symm_var, Module.Relations.Solution.fromQuotient_toQuotient, Module.Relations.Solution.π_single]

