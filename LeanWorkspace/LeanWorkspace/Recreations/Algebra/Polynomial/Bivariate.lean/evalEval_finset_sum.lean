import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_finset_sum {ι : Type*} (s : Finset ι) (x y : R) (f : ι → R[X][Y]) :
    (∑ i ∈ s, f i).evalEval x y = ∑ i ∈ s, (f i).evalEval x y := by
  simp only [evalEval, eval_finset_sum]

