import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem op_geom_sum (x : R) (n : ℕ) : op (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, op x ^ i := by
  simp

