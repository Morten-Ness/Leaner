import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R]

theorem evalEval_dvd (x y : R) {p q : R[X][Y]} : p ∣ q → p.evalEval x y ∣ q.evalEval x y := eval_dvd ∘ eval_dvd

