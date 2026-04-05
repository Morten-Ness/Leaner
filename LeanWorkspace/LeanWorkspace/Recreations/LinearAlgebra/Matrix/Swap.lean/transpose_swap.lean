import Mathlib

variable {R n : Type*} [Zero R] [One R] [DecidableEq n]

theorem transpose_swap (i j : n) : (Matrix.swap R i j).transpose = Matrix.swap R i j := by
  simp [Matrix.swap]

