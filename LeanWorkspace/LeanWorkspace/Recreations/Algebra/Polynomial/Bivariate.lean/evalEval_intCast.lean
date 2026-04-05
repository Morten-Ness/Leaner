import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Ring R]

theorem evalEval_intCast (x y : R) (n : ℤ) : (n : R[X][Y]).evalEval x y = n := by
  simp only [evalEval, eval_intCast]

