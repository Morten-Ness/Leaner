import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_zero' : Polynomial.taylor (0 : R) = LinearMap.id := LinearMap.ext Polynomial.taylor_zero

