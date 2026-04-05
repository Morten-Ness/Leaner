import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem algebraMap_eq_toLaurent (f : R[X]) : algebraMap R[X] R[T;T⁻¹] f = toLaurent f := rfl

