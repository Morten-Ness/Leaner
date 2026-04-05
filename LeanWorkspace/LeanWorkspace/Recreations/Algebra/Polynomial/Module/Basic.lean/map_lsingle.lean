import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

theorem map_lsingle (f : M →ₗ[R] M') (i : ℕ) (m : M) :
    PolynomialModule.map R' f (PolynomialModule.lsingle R i m) = PolynomialModule.lsingle R' i (f m) := PolynomialModule.map_single ..

