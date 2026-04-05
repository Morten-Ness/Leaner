import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

variable {N : Type v'} [AddCommGroup N] [Module A N]

theorem π_desc_apply (s : relations.Solution N) (x : relations.G →₀ A) :
    h.desc s (solution.π x) = s.π x := DFunLike.congr_fun (Module.Relations.Solution.IsPresentation.desc_comp_π h s) x

