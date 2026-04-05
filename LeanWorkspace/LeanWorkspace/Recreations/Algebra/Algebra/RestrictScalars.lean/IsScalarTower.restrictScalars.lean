import Mathlib

variable (R S M A : Type*)

variable [Semiring S] [AddCommMonoid M]

variable [CommSemiring R] [Algebra R S]

theorem IsScalarTower.restrictScalars [Module S M] :
    letI := Module.restrictScalars R S M
    IsScalarTower R S M :=
  IsScalarTower.of_compHom R S M

