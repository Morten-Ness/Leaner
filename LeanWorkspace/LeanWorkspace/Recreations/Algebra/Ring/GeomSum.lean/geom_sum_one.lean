import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem geom_sum_one (x : R) : ∑ i ∈ range 1, x ^ i = 1 := by simp

