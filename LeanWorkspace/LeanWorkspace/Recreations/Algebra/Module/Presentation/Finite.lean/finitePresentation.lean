import Mathlib

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]

variable (pres : Presentation A M)

theorem finitePresentation [Finite pres.G] [Finite pres.R] :
    Module.FinitePresentation A M := Module.finitePresentation_of_surjective _ pres.surjective_π (by
    rw [pres.ker_π]
    exact Submodule.fg_span (Set.finite_range _))

