import Mathlib

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

theorem counit_surjective : Function.Surjective (MvPolynomial.counit R) := MvPolynomial.ACounit_surjective ℤ R

