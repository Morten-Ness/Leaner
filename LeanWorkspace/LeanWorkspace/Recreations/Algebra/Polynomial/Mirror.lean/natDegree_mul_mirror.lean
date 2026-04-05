import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

variable [NoZeroDivisors R]

theorem natDegree_mul_mirror : (p * p.mirror).natDegree = 2 * p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, natDegree_zero, mul_zero]
  rw [natDegree_mul hp (mt Polynomial.mirror_eq_zero.mp hp), Polynomial.mirror_natDegree, two_mul]

