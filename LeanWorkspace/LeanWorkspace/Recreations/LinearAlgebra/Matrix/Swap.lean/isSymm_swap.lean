import Mathlib

variable {R n : Type*} [Zero R] [One R] [DecidableEq n]

theorem isSymm_swap (i j : n) : (Matrix.swap R i j).IsSymm := Matrix.transpose_swap i j

