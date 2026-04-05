import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_sum (x y : R) (p : R[X]) (f : ℕ → R → R[X][Y]) :
    (p.sum f).evalEval x y = p.sum fun n a => (f n a).evalEval x y := by
  simp only [evalEval, eval, eval₂_sum]

