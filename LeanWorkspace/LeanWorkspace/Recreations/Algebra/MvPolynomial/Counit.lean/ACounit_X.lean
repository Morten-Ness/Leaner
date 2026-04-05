import Mathlib

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

theorem ACounit_X (b : B) : MvPolynomial.ACounit A B (X b) = b := aeval_X _ b

