import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R]

theorem map_evalRingHom_eval (x y : R) (p : R[X][Y]) :
    (p.map <| evalRingHom x).eval y = p.evalEval x y := by
  rw [eval_map, Polynomial.eval₂_evalRingHom]

