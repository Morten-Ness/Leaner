import Mathlib

open scoped Polynomial

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

set_option backward.isDefEq.respectTransparency false in
theorem smul_apply (f : R[X]) (g : PolynomialModule R M) (n : ℕ) :
    (f • g) n = ∑ x ∈ Finset.antidiagonal n, f.coeff x.1 • g x.2 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_smul, Finsupp.add_apply, hp, hq, ← Finset.sum_add_distrib]
    congr
    ext
    rw [coeff_add, add_smul]
  | monomial f_n f_a =>
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => (monomial f_n f_a).coeff i • g j,
      PolynomialModule.monomial_smul_apply]
    simp_rw [Polynomial.coeff_monomial, ← Finset.mem_range_succ_iff]
    simp

