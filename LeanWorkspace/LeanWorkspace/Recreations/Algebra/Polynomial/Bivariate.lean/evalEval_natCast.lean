import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_natCast (x y : R) (n : ℕ) : (n : R[X][Y]).evalEval x y = n := by
  simp only [evalEval, eval_natCast]

