import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

variable [IsScalarTower R S S]

theorem smeval_assoc_X_pow (m n : ℕ) :
    p.smeval x * x ^ m * x ^ n = p.smeval x * (x ^ m * x ^ n) := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [Polynomial.smeval_add, ph, qh, add_mul]
  | monomial n a =>
    rw [Polynomial.smeval_monomial, smul_mul_assoc, smul_mul_assoc, npow_mul_assoc, ← smul_mul_assoc]

