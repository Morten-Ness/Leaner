import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem eta (f : R[X]) : Polynomial.ofFinsupp f.toFinsupp = f := by constructor

