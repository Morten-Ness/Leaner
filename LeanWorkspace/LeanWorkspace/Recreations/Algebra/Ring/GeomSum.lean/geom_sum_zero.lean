import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem geom_sum_zero (x : R) : ∑ i ∈ range 0, x ^ i = 0 := rfl

