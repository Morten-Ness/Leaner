import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

variable [NoZeroDivisors R]

theorem mirror_mul_of_domain : (p * q).mirror = p.mirror * q.mirror := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, Polynomial.mirror_zero, zero_mul]
  by_cases hq : q = 0
  · rw [hq, mul_zero, Polynomial.mirror_zero, mul_zero]
  rw [Polynomial.mirror, Polynomial.mirror, Polynomial.mirror, reverse_mul_of_domain, natTrailingDegree_mul hp hq, pow_add]
  rw [mul_assoc, ← mul_assoc q.reverse, ← X_pow_mul (p := reverse q)]
  repeat' rw [mul_assoc]

