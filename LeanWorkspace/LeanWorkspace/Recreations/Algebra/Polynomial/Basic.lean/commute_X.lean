import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem commute_X (p : R[X]) : Commute Polynomial.X p := Polynomial.X_mul

