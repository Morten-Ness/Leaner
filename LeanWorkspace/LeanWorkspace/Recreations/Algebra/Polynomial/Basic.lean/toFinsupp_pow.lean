import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_pow (a : R[X]) (n : ℕ) : (a ^ n).toFinsupp = a.toFinsupp ^ n := by
  rw [← Polynomial.ofFinsupp_pow]

