import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeffs_zero : Polynomial.coeffs (0 : R[X]) = ∅ := rfl

