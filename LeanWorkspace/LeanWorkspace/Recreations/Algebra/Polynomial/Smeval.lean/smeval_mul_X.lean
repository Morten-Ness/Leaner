import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

variable [IsScalarTower R S S]

theorem smeval_mul_X : (p * X).smeval x = p.smeval x * x := by
    induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [add_mul, Polynomial.smeval_add, ph, qh]
  | monomial n a =>
    simp only [← monomial_one_one_eq_X, monomial_mul_monomial, Polynomial.smeval_monomial, mul_one,
      npow_add, smul_mul_assoc, npow_one]

