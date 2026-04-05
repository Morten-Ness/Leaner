import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_zero : (0 : R[X]).mirror = 0 := by simp [Polynomial.mirror]

