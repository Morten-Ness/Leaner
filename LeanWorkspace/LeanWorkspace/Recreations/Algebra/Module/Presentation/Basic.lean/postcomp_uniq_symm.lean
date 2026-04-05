import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

variable {N : Type v'} [AddCommGroup N] [Module A N]

variable {solution' : relations.Solution N} (h' : solution'.IsPresentation)

theorem postcomp_uniq_symm : solution'.postcomp (Module.Relations.Solution.IsPresentation.uniq h h').symm.toLinearMap = solution := by
  simp [Module.Relations.Solution.IsPresentation.uniq]

