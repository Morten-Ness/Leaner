import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_X_pow (n : ℕ) : (Polynomial.X ^ n).toFinsupp = .single n (1 : R) := by
  rw [Polynomial.X_pow_eq_monomial, Polynomial.toFinsupp_monomial]

