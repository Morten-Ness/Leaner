import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_C (x y : R) (p : R[X]) : (C p).evalEval x y = p.eval x := by
  rw [evalEval, eval_C]

