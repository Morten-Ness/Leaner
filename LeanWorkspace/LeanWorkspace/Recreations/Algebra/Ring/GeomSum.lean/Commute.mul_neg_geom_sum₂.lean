import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem Commute.mul_neg_geom_sum₂ (h : Commute x y) (n : ℕ) :
    ((y - x) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = y ^ n - x ^ n := by
  apply op_injective
  simp only [op_mul, op_sub, op_pow]
  simp [(Commute.op h.symm).geom_sum₂_mul n]

