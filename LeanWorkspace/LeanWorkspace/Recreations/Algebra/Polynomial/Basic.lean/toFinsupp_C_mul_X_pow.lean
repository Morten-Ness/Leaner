import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_C_mul_X_pow (a : R) (n : ℕ) : (Polynomial.C a * Polynomial.X ^ n).toFinsupp = .single n a := by
  rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toFinsupp_monomial]

