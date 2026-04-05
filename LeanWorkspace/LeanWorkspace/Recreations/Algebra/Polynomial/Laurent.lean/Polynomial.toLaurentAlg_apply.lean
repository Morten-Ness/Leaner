import Mathlib

open scoped Polynomial

variable {R S : Type*}

theorem Polynomial.toLaurentAlg_apply [CommSemiring R] (f : R[X]) : Polynomial.toLaurentAlg f = toLaurent f := rfl

