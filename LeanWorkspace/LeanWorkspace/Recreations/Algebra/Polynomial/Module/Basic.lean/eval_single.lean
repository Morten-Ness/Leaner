import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

variable [Algebra R R'] [IsScalarTower R R' M']

theorem eval_single (r : R) (i : ℕ) (m : M) : PolynomialModule.eval r (PolynomialModule.single R i m) = r ^ i • m := Finsupp.sum_single_index (smul_zero _)

