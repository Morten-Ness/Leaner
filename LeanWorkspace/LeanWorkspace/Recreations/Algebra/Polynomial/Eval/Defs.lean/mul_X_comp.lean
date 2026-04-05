import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem mul_X_comp : (p * Polynomial.X).comp r = p.comp r * r := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, add_mul, Polynomial.add_comp]
  | monomial n b => simp only [pow_succ, mul_assoc, monomial_mul_X, Polynomial.monomial_comp]

