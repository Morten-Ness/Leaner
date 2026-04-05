import Mathlib

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

theorem monomial_smul_single (i : ℕ) (r : R) (j : ℕ) (m : M) :
    monomial i r • PolynomialModule.single R j m = PolynomialModule.single R (i + j) (r • m) := by
  simp only [Module.End.mul_apply, Polynomial.aeval_monomial, Module.End.pow_apply,
    Module.algebraMap_end_apply, PolynomialModule.smul_def]
  induction i generalizing r j m with
  | zero =>
    rw [Function.iterate_zero, zero_add]
    exact Finsupp.smul_single r j m
  | succ n hn =>
    rw [Function.iterate_succ, Function.comp_apply, add_assoc, ← hn]
    congr 2
    rw [Nat.one_add]
    exact Finsupp.mapDomain_single

