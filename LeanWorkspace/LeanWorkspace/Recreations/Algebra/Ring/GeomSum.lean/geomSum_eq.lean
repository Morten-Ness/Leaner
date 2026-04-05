import Mathlib

variable {R S : Type*}

variable {m k : ℕ} (x y n : ℕ)

theorem geomSum_eq (hm : 2 ≤ m) (n : ℕ) : ∑ k ∈ range n, m ^ k = (m ^ n - 1) / (m - 1) := by
  refine (Nat.div_eq_of_eq_mul_left (tsub_pos_iff_lt.2 hm) <| tsub_eq_of_eq_add ?_).symm
  simpa only [tsub_add_cancel_of_le (by lia : 1 ≤ m), eq_comm] using geom_sum_mul_add (m - 1) n

