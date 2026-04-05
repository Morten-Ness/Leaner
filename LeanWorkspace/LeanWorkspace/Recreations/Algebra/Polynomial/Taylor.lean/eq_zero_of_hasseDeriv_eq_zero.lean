import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem eq_zero_of_hasseDeriv_eq_zero (f : R[X]) (r : R)
    (h : ∀ k, (hasseDeriv k f).eval r = 0) : f = 0 := by
  rw [← Polynomial.taylor_eq_zero r]
  ext k
  rw [Polynomial.taylor_coeff, h, coeff_zero]

