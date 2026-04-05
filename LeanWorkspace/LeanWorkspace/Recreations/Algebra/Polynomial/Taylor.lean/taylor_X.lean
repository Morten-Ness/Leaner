import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_X : Polynomial.taylor r X = X + C r := X_comp

