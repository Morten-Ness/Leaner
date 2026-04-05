import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem coe_restrictScalars (V : Submodule R M) : (V.restrictScalars S : Set M) = V := rfl

