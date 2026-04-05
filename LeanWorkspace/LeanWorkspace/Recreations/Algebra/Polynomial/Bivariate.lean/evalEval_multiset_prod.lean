import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R]

theorem evalEval_multiset_prod (x y : R) (l : Multiset R[X][Y]) :
    l.prod.evalEval x y = (l.map <| evalEval x y).prod := by
  simp [evalEval, eval_multiset_prod, Multiset.map_map]

