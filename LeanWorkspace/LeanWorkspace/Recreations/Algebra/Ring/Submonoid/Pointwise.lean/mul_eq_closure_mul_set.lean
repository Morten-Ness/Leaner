import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

theorem mul_eq_closure_mul_set (M N : AddSubmonoid R) : M * N = closure (M * N : Set R) := by
  rw [← AddSubmonoid.closure_mul_closure, closure_eq, closure_eq]

