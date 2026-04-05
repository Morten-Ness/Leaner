import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_pow (n : ℕ) (r : R) (k : ℕ) : Polynomial.monomial n r ^ k = Polynomial.monomial (n * k) (r ^ k) := by
  induction k with
  | zero => simp [pow_zero, Polynomial.monomial_zero_one]
  | succ k ih => simp [pow_succ, ih, Polynomial.monomial_mul_monomial, mul_add, add_comm]

