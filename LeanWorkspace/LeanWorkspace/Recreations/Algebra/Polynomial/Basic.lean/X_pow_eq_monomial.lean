import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_pow_eq_monomial (n) : Polynomial.X ^ n = Polynomial.monomial n (1 : R) := (Polynomial.monomial_one_right_eq_X_pow n).symm

