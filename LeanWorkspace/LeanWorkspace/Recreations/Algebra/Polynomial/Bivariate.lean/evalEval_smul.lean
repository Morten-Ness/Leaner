import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_smul [DistribSMul S R] [IsScalarTower S R R] (x y : R) (s : S)
    (p : R[X][Y]) : (s • p).evalEval x y = s • p.evalEval x y := by
  simp only [evalEval, eval_smul]

