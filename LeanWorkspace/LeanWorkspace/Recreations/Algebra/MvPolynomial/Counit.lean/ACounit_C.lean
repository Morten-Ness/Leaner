import Mathlib

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

theorem ACounit_C (a : A) : MvPolynomial.ACounit A B (C a) = algebraMap A B a := aeval_C _ a

