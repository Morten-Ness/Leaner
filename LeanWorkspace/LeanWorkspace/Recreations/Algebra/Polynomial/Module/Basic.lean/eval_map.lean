import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Module R M']

variable [Algebra R R'] [IsScalarTower R R' M']

theorem eval_map (f : M →ₗ[R] M') (q : PolynomialModule R M) (r : R) :
    PolynomialModule.eval (algebraMap R R' r) (PolynomialModule.map R' f q) = f (PolynomialModule.eval r q) := by
  induction q using PolynomialModule.induction_linear with
  | zero => simp_rw [map_zero]
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | PolynomialModule.single i m => simp only [PolynomialModule.map_single, PolynomialModule.eval_single, PolynomialModule.map_smul f]; module

