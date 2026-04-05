import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_add (x y : R) (p q : R[X][Y]) :
    (p + q).evalEval x y = p.evalEval x y + q.evalEval x y := by
  simp only [evalEval, eval_add]

