import Mathlib

open scoped Algebra

variable {R S} [CommSemiring R] [Semiring S] [Algebra R S]

variable {M N} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S M] [IsScalarTower R S M]

variable [Module R N] [Module S N] [IsScalarTower R S N]

variable (h : Function.Surjective (algebraMap R S))

theorem LinearEquiv.extendScalarsOfSurjective_symm (f : M ≃ₗ[R] N) :
    (f.extendScalarsOfSurjective h).symm = f.symm.extendScalarsOfSurjective h := rfl

