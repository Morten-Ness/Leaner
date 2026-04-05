import Mathlib

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

theorem counitNat_surjective : Function.Surjective (MvPolynomial.counitNat A) := MvPolynomial.ACounit_surjective ℕ A

