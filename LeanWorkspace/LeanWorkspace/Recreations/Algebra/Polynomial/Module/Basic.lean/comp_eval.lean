import Mathlib

open scoped Polynomial

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

variable [Algebra R R'] [IsScalarTower R R' M']

theorem comp_eval (p : R[X]) (q : PolynomialModule R M) (r : R) :
    PolynomialModule.eval r (PolynomialModule.comp p q) = PolynomialModule.eval (p.eval r) q := by
  rw [← LinearMap.comp_apply]
  induction q using PolynomialModule.induction_linear with
  | zero => simp_rw [map_zero]
  | add _ _ e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | PolynomialModule.single i m =>
    rw [LinearMap.comp_apply, PolynomialModule.comp_single, PolynomialModule.eval_single, PolynomialModule.eval_smul, PolynomialModule.eval_single, eval_pow]
    module

