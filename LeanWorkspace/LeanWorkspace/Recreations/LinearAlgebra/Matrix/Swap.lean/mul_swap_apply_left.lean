import Mathlib

variable {R n m : Type*} [Semiring R] [DecidableEq n]

variable [Fintype n]

theorem mul_swap_apply_left (i j : n) (a : m) (g : Matrix m n R) :
    (g * Matrix.swap R i j) a i = g a j := by
  simp [Matrix.swap, PEquiv.mul_toMatrix_toPEquiv]

