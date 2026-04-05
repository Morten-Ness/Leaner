import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_zero_one : Polynomial.monomial 0 (1 : R) = 1 := rfl

