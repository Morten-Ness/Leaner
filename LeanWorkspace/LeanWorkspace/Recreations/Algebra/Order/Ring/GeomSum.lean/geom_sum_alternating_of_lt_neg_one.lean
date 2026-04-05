import Mathlib

variable {R : Type*}

variable [Ring R]

variable [PartialOrder R]

variable [IsStrictOrderedRing R] {n : ℕ} {x : R}

theorem geom_sum_alternating_of_lt_neg_one (hx : x + 1 < 0) (hn : 1 < n) :
    if Even n then ∑ i ∈ range n, x ^ i < 0 else 1 < ∑ i ∈ range n, x ^ i := by
  have hx0 : x < 0 := (le_add_of_nonneg_right zero_le_one).trans_lt hx
  refine Nat.le_induction ?_ ?_ n (show 2 ≤ n from hn)
  · simp only [geom_sum_two, lt_add_iff_pos_left, ite_true, hx, even_two]
  clear hn
  intro n _ ihn
  simp only [Nat.even_add_one, geom_sum_succ]
  split_ifs at ihn ⊢ with hn'
  · rw [lt_add_iff_pos_left]
    exact mul_pos_of_neg_of_neg hx0 ihn
  · grw [← hx]
    gcongr
    simpa only [mul_one] using mul_lt_mul_of_neg_left ihn hx0

