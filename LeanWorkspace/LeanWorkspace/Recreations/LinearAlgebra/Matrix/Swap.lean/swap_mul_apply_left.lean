import Mathlib

variable {R n m : Type*} [Semiring R] [DecidableEq n]

variable [Fintype n]

theorem swap_mul_apply_left (i j : n) (a : m) (g : Matrix n m R) :
    (Matrix.swap R i j * g) i a = g j a := by
  simp [Matrix.swap, PEquiv.toMatrix_toPEquiv_mul]

