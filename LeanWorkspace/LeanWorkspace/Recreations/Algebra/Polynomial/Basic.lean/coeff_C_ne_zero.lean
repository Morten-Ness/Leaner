import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_C_ne_zero (h : n ≠ 0) : (Polynomial.C a).coeff n = 0 := by rw [Polynomial.coeff_C, if_neg h]

