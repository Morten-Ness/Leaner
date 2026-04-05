import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_C (x : R) : Polynomial.taylor r (C x) = C x := C_comp

