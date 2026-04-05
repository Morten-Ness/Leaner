import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) :
    Polynomial.monomial n r * Polynomial.X ^ k = Polynomial.monomial (n + k) r := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, add_assoc]

