import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_map_C (x y : R) (p : R[X]) : (p.map C).evalEval x y = p.eval y := by
  rw [evalEval, eval_map_apply, eval_C]

