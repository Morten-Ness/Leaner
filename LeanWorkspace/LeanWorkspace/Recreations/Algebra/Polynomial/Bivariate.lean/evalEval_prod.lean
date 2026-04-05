import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R]

theorem evalEval_prod {ι : Type*} (s : Finset ι) (x y : R) (p : ι → R[X][Y]) :
    (∏ j ∈ s, p j).evalEval x y = ∏ j ∈ s, (p j).evalEval x y := by
  simp only [evalEval, eval_prod]

