import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem restrictScalars_mono {s t : Submodule R M} (hst : s ≤ t) :
    s.restrictScalars S ≤ t.restrictScalars S := Submodule.restrictScalars_monotone S R M hst

