import Mathlib

variable {R n m : Type*} [Semiring R] [DecidableEq n]

variable [Fintype n]

theorem swap_mul_apply_right (i j : n) (a : m) (g : Matrix n m R) :
    (Matrix.swap R i j * g) j a = g i a := by
  rw [Matrix.swap_comm, Matrix.swap_mul_apply_left]

