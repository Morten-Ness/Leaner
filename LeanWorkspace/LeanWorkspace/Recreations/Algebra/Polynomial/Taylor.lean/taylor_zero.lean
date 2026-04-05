import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_zero (f : R[X]) : Polynomial.taylor 0 f = f := by rw [Polynomial.taylor_apply, C_0, add_zero, comp_X]

