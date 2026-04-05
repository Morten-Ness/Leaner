import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_one_zero : Polynomial.coeff (1 : R[X]) 0 = 1 := by
  simp [Polynomial.coeff_one]

