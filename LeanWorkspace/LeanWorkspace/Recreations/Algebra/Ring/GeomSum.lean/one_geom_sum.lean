import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem one_geom_sum (n : ℕ) : ∑ i ∈ range n, (1 : R) ^ i = n := by simp

