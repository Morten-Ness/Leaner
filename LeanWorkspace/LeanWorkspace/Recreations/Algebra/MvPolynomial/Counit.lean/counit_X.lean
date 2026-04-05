import Mathlib

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

theorem counit_X (r : R) : MvPolynomial.counit R (X r) = r := MvPolynomial.ACounit_X _ _

