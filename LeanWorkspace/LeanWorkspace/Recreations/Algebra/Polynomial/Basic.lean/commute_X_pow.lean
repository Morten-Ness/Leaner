import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem commute_X_pow (p : R[X]) (n : ℕ) : Commute (Polynomial.X ^ n) p := Polynomial.X_pow_mul

