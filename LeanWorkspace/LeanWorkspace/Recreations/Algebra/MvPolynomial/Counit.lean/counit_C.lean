import Mathlib

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

theorem counit_C (n : ℤ) : MvPolynomial.counit R (C n) = n := MvPolynomial.ACounit_C _ _

