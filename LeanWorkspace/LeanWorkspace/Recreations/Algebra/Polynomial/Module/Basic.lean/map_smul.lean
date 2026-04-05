import Mathlib

open scoped Polynomial

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

variable [Algebra R R'] [IsScalarTower R R' M']

theorem map_smul (f : M →ₗ[R] M') (p : R[X]) (q : PolynomialModule R M) :
    PolynomialModule.map R' f (p • q) = p.map (algebraMap R R') • PolynomialModule.map R' f q := by
  induction q using PolynomialModule.induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | PolynomialModule.single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, e₁, e₂, Polynomial.map_add, add_smul]
    | monomial => rw [PolynomialModule.monomial_smul_single, PolynomialModule.map_single, Polynomial.map_monomial, PolynomialModule.map_single,
        PolynomialModule.monomial_smul_single, f.map_smul, algebraMap_smul]

