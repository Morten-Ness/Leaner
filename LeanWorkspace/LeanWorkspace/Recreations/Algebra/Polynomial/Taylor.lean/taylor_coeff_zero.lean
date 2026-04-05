import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_coeff_zero : (Polynomial.taylor r f).coeff 0 = f.eval r := by
  rw [Polynomial.taylor_coeff, hasseDeriv_zero, LinearMap.id_apply]

