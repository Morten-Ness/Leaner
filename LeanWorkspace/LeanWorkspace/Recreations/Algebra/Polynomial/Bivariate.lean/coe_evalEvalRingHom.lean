import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R]

theorem coe_evalEvalRingHom (x y : R) : evalEvalRingHom x y = evalEval x y := rfl

