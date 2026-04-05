import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem zero_geom_sum : ∀ {n}, ∑ i ∈ range n, (0 : R) ^ i = if n = 0 then 0 else 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [geom_sum_succ']
    simp [zero_geom_sum]
