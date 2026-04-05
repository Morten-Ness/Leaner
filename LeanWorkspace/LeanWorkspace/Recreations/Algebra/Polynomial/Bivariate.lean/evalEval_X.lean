import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_X (x y : R) : X.evalEval x y = y := by
  rw [evalEval, eval_X, eval_C]

