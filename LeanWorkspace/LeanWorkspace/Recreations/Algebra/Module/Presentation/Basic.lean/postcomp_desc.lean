import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

variable {N : Type v'} [AddCommGroup N] [Module A N]

theorem postcomp_desc (s : relations.Solution N) :
    solution.postcomp (h.desc s) = s := by aesop

