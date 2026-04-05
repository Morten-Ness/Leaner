import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem abs_sub_left_of_mem_uIcc (h : c ∈ [[a, b]]) : |c - a| ≤ |b - a| := Set.abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc_left h

