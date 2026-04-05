import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

theorem ne_zero_of_ofFn_ne_zero {n : ℕ} {v : Fin n → R} (h : Polynomial.ofFn n v ≠ 0) : n ≠ 0 := by
  contrapose! h
  subst h
  simp

