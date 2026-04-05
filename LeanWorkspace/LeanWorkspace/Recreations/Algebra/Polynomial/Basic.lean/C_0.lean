import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_0 : Polynomial.C (0 : R) = 0 := by simp

