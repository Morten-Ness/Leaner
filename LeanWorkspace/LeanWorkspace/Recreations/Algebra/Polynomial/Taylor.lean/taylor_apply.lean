import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_apply : Polynomial.taylor r f = f.comp (X + C r) := rfl

