import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_pow : Polynomial.C (a ^ n) = Polynomial.C a ^ n := Polynomial.C.map_pow a n

