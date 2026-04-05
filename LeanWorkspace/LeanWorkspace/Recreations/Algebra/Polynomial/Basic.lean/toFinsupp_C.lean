import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_C (a : R) : (Polynomial.C a).toFinsupp = single 0 a := rfl

