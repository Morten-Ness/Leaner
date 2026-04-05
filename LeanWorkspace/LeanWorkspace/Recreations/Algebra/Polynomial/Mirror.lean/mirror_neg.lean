import Mathlib

variable {R : Type*} [Ring R] (p q : R[X])

theorem mirror_neg : (-p).mirror = -p.mirror := by
  rw [Polynomial.mirror, Polynomial.mirror, reverse_neg, natTrailingDegree_neg, neg_mul_eq_neg_mul]

