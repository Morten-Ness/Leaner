import Mathlib

open scoped Polynomial

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

variable [Algebra R R'] [IsScalarTower R R' M']

theorem eval_smul (p : R[X]) (q : PolynomialModule R M) (r : R) :
    PolynomialModule.eval r (p • q) = p.eval r • PolynomialModule.eval r q := by
  induction q using PolynomialModule.induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | PolynomialModule.single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, Polynomial.eval_add, e₁, e₂, add_smul]
    | monomial => simp only [PolynomialModule.monomial_smul_single, Polynomial.eval_monomial, PolynomialModule.eval_single]; module

