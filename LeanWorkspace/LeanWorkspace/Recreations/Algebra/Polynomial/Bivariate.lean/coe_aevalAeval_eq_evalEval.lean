import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem coe_aevalAeval_eq_evalEval (x y : A) : ⇑(aevalAeval x y) = evalEval x y := by
  ext
  simp [aeval, aevalEquiv]

