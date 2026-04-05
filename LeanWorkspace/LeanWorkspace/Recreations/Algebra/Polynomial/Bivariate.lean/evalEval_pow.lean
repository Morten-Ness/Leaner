import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R]

theorem evalEval_pow (x y : R) (p : R[X][Y]) (n : ℕ) : (p ^ n).evalEval x y = p.evalEval x y ^ n := by
  simp only [evalEval, eval_pow]

