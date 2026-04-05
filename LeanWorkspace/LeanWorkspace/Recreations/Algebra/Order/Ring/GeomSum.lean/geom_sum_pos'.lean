import Mathlib

variable {R : Type*}

variable [Ring R]

variable [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ} {x : R}

theorem geom_sum_pos' (hx : 0 < x + 1) (hn : n ≠ 0) : 0 < ∑ i ∈ range n, x ^ i := by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  obtain hx' | hx' := lt_or_ge x 0
  · exact (geom_sum_pos_and_lt_one hx' hx n.one_lt_succ_succ).1
  · exact geom_sum_pos hx' (by simp)

