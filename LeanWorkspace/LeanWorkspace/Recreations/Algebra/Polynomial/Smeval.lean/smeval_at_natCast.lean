import Mathlib

variable (R : Type*) [Semiring R] (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [Pow S ℕ] (x : S)

variable [NatPowAssoc S]

theorem smeval_at_natCast (q : ℕ[X]) : ∀ (n : ℕ), q.smeval (n : S) = q.smeval n := by
  induction q using Polynomial.induction_on' with
  | add p q ph qh =>
    intro n
    simp only [Polynomial.smeval_add, ph, qh, Nat.cast_add]
  | monomial n a =>
    intro n
    rw [Polynomial.smeval_monomial, Polynomial.smeval_monomial, nsmul_eq_mul, smul_eq_mul, Nat.cast_mul, Nat.cast_npow]

