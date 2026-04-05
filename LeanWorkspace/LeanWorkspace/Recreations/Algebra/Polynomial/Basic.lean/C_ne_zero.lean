import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_ne_zero : Polynomial.C a ≠ 0 ↔ a ≠ 0 := Polynomial.C_eq_zero.not

