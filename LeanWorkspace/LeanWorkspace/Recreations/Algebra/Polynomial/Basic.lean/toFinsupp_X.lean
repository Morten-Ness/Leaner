import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_X : Polynomial.X.toFinsupp = .single 1 (1 : R) := rfl

