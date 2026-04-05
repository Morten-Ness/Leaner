import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [Semiring R]

theorem pow_eq_closure_pow_set (s : AddSubmonoid R) (n : ℕ) :
    s ^ n = closure ((s : Set R) ^ n) := by
  rw [← AddSubmonoid.closure_pow, closure_eq]

