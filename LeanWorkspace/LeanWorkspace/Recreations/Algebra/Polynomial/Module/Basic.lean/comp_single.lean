import Mathlib

open scoped Polynomial

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

variable [Algebra R R'] [IsScalarTower R R' M']

theorem comp_single (p : R[X]) (i : ℕ) (m : M) : PolynomialModule.comp p (PolynomialModule.single R i m) = p ^ i • PolynomialModule.single R 0 m := by
  rw [comp_apply, PolynomialModule.map_single, PolynomialModule.eval_single]
  rfl

