import Mathlib

open scoped Algebra

variable (R : Type u) (S : Type v) (M : Type w)

variable [CommSemiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMulCommClass S R M] [SMul R S] [IsScalarTower R S M]

theorem algebraMap_end_apply (a : R) (m : M) : algebraMap R (End S M) a m = a • m := rfl

