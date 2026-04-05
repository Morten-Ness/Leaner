import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_X_pow (H : ¬(1 : R) = 0) (n : ℕ) : (Polynomial.X ^ n : R[X]).support = singleton n := by
  convert Polynomial.support_monomial n H
  exact Polynomial.X_pow_eq_monomial n

