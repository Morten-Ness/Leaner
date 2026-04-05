import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R] [Semiring S] (f : R →+* S) (p : R[X][Y]) (q : R[X])

theorem map_mapRingHom_evalEval (x y : R) :
    (p.map <| mapRingHom f).evalEval (f x) (f y) = f (p.evalEval x y) := by
  rw [evalEval, ← Polynomial.map_mapRingHom_eval_map_eval, map_C]

