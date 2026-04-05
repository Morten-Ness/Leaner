import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_one (x y : R) : (1 : R[X][Y]).evalEval x y = 1 := by
  simp only [evalEval, eval_one]

