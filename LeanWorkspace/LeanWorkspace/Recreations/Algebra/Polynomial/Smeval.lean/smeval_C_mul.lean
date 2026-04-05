import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

theorem smeval_C_mul : (C r * p).smeval x = r • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [mul_add, Polynomial.smeval_add, ph, qh, smul_add]
  | monomial n b => simp only [C_mul_monomial, Polynomial.smeval_monomial, mul_smul]

