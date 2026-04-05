import Mathlib

variable {R : Type*}

variable [Ring R]

variable [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ} {x : R}

theorem Odd.geom_sum_pos (h : Odd n) : 0 < ∑ i ∈ range n, x ^ i := by
  rcases n with (_ | _ | k)
  · exact (Nat.not_odd_zero h).elim
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  rw [← Nat.not_even_iff_odd] at h
  rcases lt_trichotomy (x + 1) 0 with (hx | hx | hx)
  · have := geom_sum_alternating_of_lt_neg_one hx k.one_lt_succ_succ
    simp only [h, if_false] at this
    exact zero_lt_one.trans this
  · simp only [eq_neg_of_add_eq_zero_left hx, h, neg_one_geom_sum, if_false, zero_lt_one]
  · exact geom_sum_pos' hx k.succ.succ_ne_zero

