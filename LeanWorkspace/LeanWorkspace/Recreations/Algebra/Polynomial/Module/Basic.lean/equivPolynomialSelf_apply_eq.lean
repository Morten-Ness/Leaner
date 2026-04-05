import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

theorem equivPolynomialSelf_apply_eq (p : PolynomialModule R R) :
    PolynomialModule.equivPolynomialSelf p = PolynomialModule.equivPolynomial p := rfl

