import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R]

theorem evalEval_surjective (x y : R) : Function.Surjective <| evalEval x y := fun y => ⟨CC y, Polynomial.evalEval_CC ..⟩

