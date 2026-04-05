import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_eq_one {a : R[X]} : a.toFinsupp = 1 ↔ a = 1 := by
  rw [← Polynomial.toFinsupp_one, Polynomial.toFinsupp_inj]

