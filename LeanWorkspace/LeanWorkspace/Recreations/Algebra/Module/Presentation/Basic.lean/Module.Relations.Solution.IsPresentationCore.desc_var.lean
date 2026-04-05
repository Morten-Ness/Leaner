import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M}

theorem desc_var (h : Module.Relations.Solution.IsPresentationCore.{w'} solution)
    {N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N) (g : relations.G) :
    h.desc s (solution.var g) = s.var g := Module.Relations.Solution.congr_var (Module.Relations.Solution.IsPresentation.postcomp_desc h s) g

