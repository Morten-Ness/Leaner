import Mathlib

variable {R : Type*}

theorem Nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i ∈ range n, a / b ^ i ≤ a * b / (b - 1) := by
  refine (Nat.le_div_iff_mul_le <| tsub_pos_of_lt hb).2 ?_
  rcases n with - | n
  · rw [sum_range_zero, zero_mul]
    exact Nat.zero_le _
  rw [mul_comm]
  exact (Nat.pred_mul_geom_sum_le a b n).trans tsub_le_self

