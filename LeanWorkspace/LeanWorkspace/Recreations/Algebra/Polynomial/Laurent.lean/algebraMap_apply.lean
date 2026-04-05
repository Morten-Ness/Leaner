import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem algebraMap_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (r : R) :
    algebraMap R (LaurentPolynomial A) r = Polynomial.C (algebraMap R A r) := rfl

