import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

theorem monomial_smul_lsingle (i : ℕ) (r : R) (j : ℕ) (m : M) :
    (monomial i) r • PolynomialModule.lsingle R j m = PolynomialModule.lsingle R (i + j) (r • m) := PolynomialModule.monomial_smul_single ..

