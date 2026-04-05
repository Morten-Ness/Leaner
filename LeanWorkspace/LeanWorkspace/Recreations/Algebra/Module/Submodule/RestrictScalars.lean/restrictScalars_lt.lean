import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem restrictScalars_lt {s t : Submodule R M} :
    s.restrictScalars S < t.restrictScalars S ↔ s < t := Iff.rfl

