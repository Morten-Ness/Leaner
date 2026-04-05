import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem toIntSubmodule_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    N.toAddSubgroup.toIntSubmodule = N.restrictScalars ℤ := rfl

