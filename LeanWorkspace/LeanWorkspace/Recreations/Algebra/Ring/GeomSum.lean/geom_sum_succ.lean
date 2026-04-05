import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem geom_sum_succ {x : R} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = (x * ∑ i ∈ range n, x ^ i) + 1 := by
  simp only [mul_sum, ← pow_succ', sum_range_succ', pow_zero]

