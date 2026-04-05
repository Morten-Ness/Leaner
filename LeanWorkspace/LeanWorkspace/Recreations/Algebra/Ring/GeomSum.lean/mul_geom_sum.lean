import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem mul_geom_sum (x : R) (n : ℕ) : ((x - 1) * ∑ i ∈ range n, x ^ i) = x ^ n - 1 := op_injective <| by simpa using geom_sum_mul (op x) n

