import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_zero (n : ℕ) : Polynomial.coeff (0 : R[X]) n = 0 := rfl

