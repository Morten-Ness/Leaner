import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem abs_sub_le_of_uIcc_subset_uIcc (h : [[c, d]] ⊆ [[a, b]]) : |d - c| ≤ |b - a| := by
  rw [← max_sub_min_eq_abs, ← max_sub_min_eq_abs]
  rw [uIcc_subset_uIcc_iff_le] at h
  exact sub_le_sub h.2 h.1

