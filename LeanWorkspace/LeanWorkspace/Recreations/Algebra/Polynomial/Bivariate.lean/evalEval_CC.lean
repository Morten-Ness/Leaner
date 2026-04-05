import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_CC (x y : R) (p : R) : (CC p).evalEval x y = p := by
  rw [Polynomial.evalEval_C, eval_C]

