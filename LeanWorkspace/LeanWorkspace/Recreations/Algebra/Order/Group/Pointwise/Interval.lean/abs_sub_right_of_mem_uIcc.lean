import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem abs_sub_right_of_mem_uIcc (h : c ∈ [[a, b]]) : |b - c| ≤ |b - a| := Set.abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc_right h

