import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_C_mul : (Polynomial.C a * p).eval x = a * p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [mul_add, Polynomial.eval_add, ph, qh]
  | monomial n b => simp only [mul_assoc, C_mul_monomial, Polynomial.eval_monomial]

