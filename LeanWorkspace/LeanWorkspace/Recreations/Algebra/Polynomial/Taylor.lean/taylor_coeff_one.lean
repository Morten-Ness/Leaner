import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_coeff_one : (Polynomial.taylor r f).coeff 1 = f.derivative.eval r := by
  rw [Polynomial.taylor_coeff, hasseDeriv_one]

