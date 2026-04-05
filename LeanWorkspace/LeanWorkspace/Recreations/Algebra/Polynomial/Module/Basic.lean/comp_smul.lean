import Mathlib

open scoped Polynomial

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

variable [Algebra R R'] [IsScalarTower R R' M']

theorem comp_smul (p p' : R[X]) (q : PolynomialModule R M) :
    PolynomialModule.comp p (p' • q) = p'.comp p • PolynomialModule.comp p q := by
  rw [comp_apply, PolynomialModule.map_smul, PolynomialModule.eval_smul, Polynomial.comp, Polynomial.eval_map, comp_apply]
  rfl

