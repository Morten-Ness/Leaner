import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem geom_sum_two {x : R} : ∑ i ∈ range 2, x ^ i = x + 1 := by simp [geom_sum_succ']

