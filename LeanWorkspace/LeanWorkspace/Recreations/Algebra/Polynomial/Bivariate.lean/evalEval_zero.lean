import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_zero (x y : R) : (0 : R[X][Y]).evalEval x y = 0 := by
  simp only [evalEval, eval_zero]

