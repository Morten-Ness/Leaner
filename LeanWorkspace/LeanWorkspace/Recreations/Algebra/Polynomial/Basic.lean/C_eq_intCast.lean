import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

theorem C_eq_intCast (n : ℤ) : Polynomial.C (n : R) = n := by simp

