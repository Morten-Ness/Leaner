import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_eq_natCast (n : ℕ) : Polynomial.C (n : R) = (n : R[X]) := map_natCast Polynomial.C n

