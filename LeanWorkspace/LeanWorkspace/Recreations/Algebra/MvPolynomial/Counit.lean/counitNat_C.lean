import Mathlib

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

theorem counitNat_C (n : ℕ) : MvPolynomial.counitNat A (C n) = n := MvPolynomial.ACounit_C _ _

