import Mathlib

variable {ι α β : Type*}

theorem abs_sum_le_sum_abs [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Multiset α} :
    |s.sum| ≤ (s.map abs).sum := le_sum_of_subadditive _ abs_zero.le abs_add_le s

