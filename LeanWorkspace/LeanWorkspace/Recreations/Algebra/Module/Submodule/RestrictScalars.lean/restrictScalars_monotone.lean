import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem restrictScalars_monotone : Monotone (Submodule.restrictScalars S : Submodule R M → Submodule S M) := (Submodule.restrictScalarsEmbedding S R M).monotone

