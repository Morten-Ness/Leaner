import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_zero_left (a : R) : Polynomial.monomial 0 a = Polynomial.C a := rfl

