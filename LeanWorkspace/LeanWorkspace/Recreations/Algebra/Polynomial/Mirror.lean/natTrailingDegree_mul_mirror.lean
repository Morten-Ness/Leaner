import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

variable [NoZeroDivisors R]

theorem natTrailingDegree_mul_mirror :
    (p * p.mirror).natTrailingDegree = 2 * p.natTrailingDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, natTrailingDegree_zero, mul_zero]
  rw [natTrailingDegree_mul hp (mt Polynomial.mirror_eq_zero.mp hp), Polynomial.mirror_natTrailingDegree, two_mul]

