import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

theorem single_smul (i : ℕ) (r : R) (m : M) : PolynomialModule.single R i (r • m) = r • PolynomialModule.single R i m := (PolynomialModule.lsingle R i).map_smul r m

