import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
    Matrix.permanent A = A default default := by simp [Matrix.permanent, univ_unique]

