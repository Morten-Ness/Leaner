import Mathlib

variable {ι α β M N P G : Type*}

variable [Group G]

theorem prod_range_div' (n : ℕ) (f : ℕ → G) :
    ((range n).map fun k ↦ f k / f (k + 1)).prod = f 0 / f n := by
  induction n with
  | zero => exact (div_self' (f 0)).symm
  | succ n h => simp [range_succ, prod_append, map_append, h]

