import Mathlib

variable (R : Type*) (m n : Type*) [Fintype m] [Finite n] [Semiring R]

theorem stdBasis_eq_single (i : m) (j : n) [DecidableEq m] [DecidableEq n] :
    Matrix.stdBasis R m n (i, j) = single i j (1 : R) := by
  simp [Matrix.stdBasis, single_eq_of_single_single]

