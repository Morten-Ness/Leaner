import Mathlib

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

theorem counitNat_X (a : A) : MvPolynomial.counitNat A (X a) = a := MvPolynomial.ACounit_X _ _

