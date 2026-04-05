import Mathlib

variable {R : Type*}

variable [Ring R]

variable [PartialOrder R]

variable [IsOrderedRing R] {x : R}

theorem geom_sum_alternating_of_le_neg_one (hx : x + 1 ≤ 0) (n : ℕ) :
    if Even n then (∑ i ∈ range n, x ^ i) ≤ 0 else 1 ≤ ∑ i ∈ range n, x ^ i := by
  have hx0 : x ≤ 0 := (le_add_of_nonneg_right zero_le_one).trans hx
  induction n with
  | zero => simp only [range_zero, sum_empty, le_refl, ite_true, Even.zero]
  | succ n ih =>
    simp only [Nat.even_add_one, geom_sum_succ]
    split_ifs at ih ⊢ with h
    · rw [le_add_iff_nonneg_left]
      exact mul_nonneg_of_nonpos_of_nonpos hx0 ih
    · grw [← hx]
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonpos_left ih hx0

