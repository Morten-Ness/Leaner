import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_monomial (i : ℕ) (k : R) : Polynomial.taylor r (monomial i k) = C k * (X + C r) ^ i := by
  simp [Polynomial.taylor_apply]

