import Mathlib

variable {R n m : Type*} [Semiring R] [DecidableEq n]

theorem map_swap {S : Type*} [NonAssocSemiring S] (f : R →+* S) (i j : n) :
    (Matrix.swap R i j).map f = Matrix.swap S i j := by
  simp [Matrix.swap]

