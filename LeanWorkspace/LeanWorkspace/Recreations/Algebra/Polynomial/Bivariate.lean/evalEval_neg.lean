import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Ring R]

theorem evalEval_neg (x y : R) (p : R[X][Y]) : (-p).evalEval x y = -p.evalEval x y := by
  simp only [evalEval, eval_neg]

