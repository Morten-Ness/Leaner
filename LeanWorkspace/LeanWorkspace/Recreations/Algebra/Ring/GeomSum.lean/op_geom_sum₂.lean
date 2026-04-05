import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem op_geom_sum₂ (x y : R) (n : ℕ) : ∑ i ∈ range n, op y ^ (n - 1 - i) * op x ^ i =
    ∑ i ∈ range n, op y ^ i * op x ^ (n - 1 - i) := by
  rw [← sum_range_reflect]
  refine Finset.sum_congr rfl fun j j_in => ?_
  grind

