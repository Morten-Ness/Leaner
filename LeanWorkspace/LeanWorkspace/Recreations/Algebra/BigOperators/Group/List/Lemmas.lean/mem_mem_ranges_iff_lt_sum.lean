import Mathlib

variable {ι α β M N P G : Type*}

theorem mem_mem_ranges_iff_lt_sum (l : List ℕ) {n : ℕ} :
    (∃ s ∈ l.ranges, n ∈ s) ↔ n < l.sum := by
  rw [← mem_range, ← List.ranges_flatten, mem_flatten]

