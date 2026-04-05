import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem natCast_mul (n : ℕ) (p : R[X]) : (n : R[X]) * p = n • p := (nsmul_eq_mul _ _).symm

