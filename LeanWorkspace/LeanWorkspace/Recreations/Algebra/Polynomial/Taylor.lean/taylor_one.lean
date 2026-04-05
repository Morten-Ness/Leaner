import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_one : Polynomial.taylor r (1 : R[X]) = C 1 := Polynomial.taylor_C r 1

