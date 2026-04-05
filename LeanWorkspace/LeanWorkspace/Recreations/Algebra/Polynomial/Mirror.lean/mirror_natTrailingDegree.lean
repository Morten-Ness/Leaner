import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_natTrailingDegree : p.mirror.natTrailingDegree = p.natTrailingDegree := by
  by_cases hp : p = 0
  · rw [hp, Polynomial.mirror_zero]
  · rw [Polynomial.mirror, natTrailingDegree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
      natTrailingDegree_reverse, zero_add]

