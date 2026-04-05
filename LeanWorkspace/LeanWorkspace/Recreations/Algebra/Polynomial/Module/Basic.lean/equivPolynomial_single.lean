import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

theorem equivPolynomial_single {S : Type*} [CommRing S] [Algebra R S] (n : ℕ) (x : S) :
    PolynomialModule.equivPolynomial (PolynomialModule.single R n x) = monomial n x := rfl

