import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

variable [SMulCommClass R S S]

theorem smeval_X_mul : (X * p).smeval x = x * p.smeval x := by
    induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [Polynomial.smeval_add, ph, qh, mul_add]
  | monomial n a =>
    rw [← monomial_one_one_eq_X, monomial_mul_monomial, Polynomial.smeval_monomial, one_mul, npow_add,
      npow_one, ← mul_smul_comm, Polynomial.smeval_monomial]

