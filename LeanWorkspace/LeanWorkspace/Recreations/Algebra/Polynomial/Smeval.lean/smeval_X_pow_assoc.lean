import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

variable [SMulCommClass R S S]

theorem smeval_X_pow_assoc (m n : ℕ) :
    x ^ m * x ^ n * p.smeval x = x ^ m * (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [Polynomial.smeval_add, ph, qh, mul_add]
  | monomial n a => simp only [Polynomial.smeval_monomial, mul_smul_comm, npow_mul_assoc]

