import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R]

theorem eval₂_evalRingHom (x : R) : eval₂ (evalRingHom x) = evalEval x := by
  ext1; rw [← Polynomial.coe_evalEvalRingHom, Polynomial.evalEvalRingHom_eq, coe_eval₂RingHom]

