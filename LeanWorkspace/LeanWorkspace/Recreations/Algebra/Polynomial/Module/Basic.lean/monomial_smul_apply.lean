import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

theorem monomial_smul_apply (i : ℕ) (r : R) (g : PolynomialModule R M) (n : ℕ) :
    (monomial i r • g) n = ite (i ≤ n) (r • g (n - i)) 0 := by
  induction g using PolynomialModule.induction_linear with
  | zero => simp only [smul_zero, PolynomialModule.zero_apply, ite_self]
  | add p q hp hq =>
    simp only [smul_add, PolynomialModule.add_apply, hp, hq]
    split_ifs
    exacts [rfl, zero_add 0]
  | PolynomialModule.single =>
    rw [PolynomialModule.monomial_smul_single, PolynomialModule.single_apply, PolynomialModule.single_apply, smul_ite, smul_zero, ← ite_and]
    grind

