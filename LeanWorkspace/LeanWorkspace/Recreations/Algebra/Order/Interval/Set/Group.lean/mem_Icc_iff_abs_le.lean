import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem mem_Icc_iff_abs_le {R : Type*}
    [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {x y z : R} :
    |x - y| ≤ z ↔ y ∈ Icc (x - z) (x + z) := abs_le.trans <| and_comm.trans <| and_congr sub_le_comm neg_le_sub_iff_le_add

