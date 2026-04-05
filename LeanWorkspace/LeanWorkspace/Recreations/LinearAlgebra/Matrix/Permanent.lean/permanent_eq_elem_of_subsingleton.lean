import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) :
    Matrix.permanent A = A k k := by
  have := uniqueOfSubsingleton k
  convert Matrix.permanent_unique A

