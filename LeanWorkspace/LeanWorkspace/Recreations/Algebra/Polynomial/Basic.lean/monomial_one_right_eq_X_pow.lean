import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_one_right_eq_X_pow (n : ℕ) : Polynomial.monomial n (1 : R) = Polynomial.X ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← ih, ← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_mul_monomial, mul_one]

