import Mathlib

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ] [Module R S]
  (x : S)

theorem smeval_smul (r : R) : (r • p).smeval x = r • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => rw [smul_add, Polynomial.smeval_add, ph, qh, ← smul_add, Polynomial.smeval_add]
  | monomial n a => rw [smul_monomial, Polynomial.smeval_monomial, Polynomial.smeval_monomial, smul_assoc]

