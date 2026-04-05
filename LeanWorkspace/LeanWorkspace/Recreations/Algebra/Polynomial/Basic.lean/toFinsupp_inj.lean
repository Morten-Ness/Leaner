import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_inj {a b : R[X]} : a.toFinsupp = b.toFinsupp ↔ a = b := Polynomial.toFinsupp_injective.eq_iff

