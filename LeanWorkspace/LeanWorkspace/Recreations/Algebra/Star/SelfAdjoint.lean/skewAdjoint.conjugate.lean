import Mathlib

variable {R A : Type*}

variable [Ring R] [StarRing R]

theorem conjugate {x : R} (hx : x ∈ skewAdjoint R) (z : R) : z * x * star z ∈ skewAdjoint R := by
  simp only [skewAdjoint.mem_iff, star_mul, star_star, skewAdjoint.mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

