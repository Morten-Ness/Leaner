import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem geom_sum_mul_neg (x : R) (n : ℕ) : (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  have := congr_arg Neg.neg (geom_sum_mul x n)
  rw [neg_sub, ← mul_neg, neg_sub] at this
  exact this

