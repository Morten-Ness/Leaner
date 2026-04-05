import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_mul : Polynomial.C (a * b) = Polynomial.C a * Polynomial.C b := Polynomial.C.map_mul a b

