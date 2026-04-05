import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_apply_one (hk : 0 < k) : Polynomial.hasseDeriv k (1 : R[X]) = 0 := by
  rw [← C_1, Polynomial.hasseDeriv_C k _ hk]

