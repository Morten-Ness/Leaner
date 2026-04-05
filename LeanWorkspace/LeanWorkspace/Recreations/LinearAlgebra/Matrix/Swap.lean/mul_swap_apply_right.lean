import Mathlib

variable {R n m : Type*} [Semiring R] [DecidableEq n]

variable [Fintype n]

theorem mul_swap_apply_right (i j : n) (a : m) (g : Matrix m n R) :
    (g * Matrix.swap R i j) a j = g a i := by
  rw [Matrix.swap_comm, Matrix.mul_swap_apply_left]

