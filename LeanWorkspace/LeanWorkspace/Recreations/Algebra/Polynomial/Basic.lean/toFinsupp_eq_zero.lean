import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_eq_zero {a : R[X]} : a.toFinsupp = 0 ↔ a = 0 := by
  rw [← Polynomial.toFinsupp_zero, Polynomial.toFinsupp_inj]

