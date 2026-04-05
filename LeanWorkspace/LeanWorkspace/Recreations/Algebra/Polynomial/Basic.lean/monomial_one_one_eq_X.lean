import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_one_one_eq_X : Polynomial.monomial 1 (1 : R) = Polynomial.X := rfl

