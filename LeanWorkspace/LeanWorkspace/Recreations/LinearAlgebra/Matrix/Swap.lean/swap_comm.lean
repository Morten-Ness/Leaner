import Mathlib

variable {R n : Type*} [Zero R] [One R] [DecidableEq n]

theorem swap_comm (i j : n) :
    Matrix.swap R i j = Matrix.swap R j i := by
  simp only [Matrix.swap, Equiv.swap_comm]

