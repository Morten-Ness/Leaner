import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_zero {N : ℕ} : Polynomial.reflect N (0 : R[X]) = 0 := rfl

