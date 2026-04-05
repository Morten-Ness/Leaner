import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

set_option backward.inferInstanceAs.wrap.data false in
theorem zero_apply (i : ℕ) : (0 : PolynomialModule R M) i = 0 := Finsupp.zero_apply

