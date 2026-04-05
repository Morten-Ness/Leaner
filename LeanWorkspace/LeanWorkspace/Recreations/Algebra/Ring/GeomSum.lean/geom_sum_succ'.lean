import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem geom_sum_succ' {x : R} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = x ^ n + ∑ i ∈ range n, x ^ i := (sum_range_succ _ _).trans (add_comm _ _)

