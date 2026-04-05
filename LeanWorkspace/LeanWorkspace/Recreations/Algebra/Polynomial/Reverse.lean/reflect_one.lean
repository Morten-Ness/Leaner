import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_one (n : ℕ) : (1 : R[X]).reflect n = Polynomial.X ^ n := by
  rw [← C.map_one, Polynomial.reflect_C, map_one, one_mul]

