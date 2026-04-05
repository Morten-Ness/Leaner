import Mathlib

variable {R n : Type*} [Zero R] [One R] [DecidableEq n]

theorem conjTranspose_swap {R : Type*} [NonAssocSemiring R] [StarRing R] (i j : n) :
    (Matrix.swap R i j).conjTranspose = Matrix.swap R i j := by
  simp [Matrix.swap]

