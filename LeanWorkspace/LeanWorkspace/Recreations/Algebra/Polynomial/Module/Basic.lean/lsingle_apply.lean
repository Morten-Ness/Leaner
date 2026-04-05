import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

theorem lsingle_apply (i : ℕ) (m : M) (n : ℕ) : PolynomialModule.lsingle R i m n = ite (i = n) m 0 := Finsupp.single_apply

