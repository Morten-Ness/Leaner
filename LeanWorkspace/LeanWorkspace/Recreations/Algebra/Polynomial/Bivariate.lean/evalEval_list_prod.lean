import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R]

theorem evalEval_list_prod (x y : R) (l : List R[X][Y]) :
    l.prod.evalEval x y = (l.map <| evalEval x y).prod := by
  simp only [evalEval, eval_list_prod, List.map_map]
  rfl -- todo: add the missing lemma

