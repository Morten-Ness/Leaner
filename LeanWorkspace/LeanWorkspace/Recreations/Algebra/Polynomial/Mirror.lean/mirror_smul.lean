import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

variable [NoZeroDivisors R]

theorem mirror_smul (a : R) : (a • p).mirror = a • p.mirror := by
  rw [← C_mul', ← C_mul', Polynomial.mirror_mul_of_domain, Polynomial.mirror_C]

