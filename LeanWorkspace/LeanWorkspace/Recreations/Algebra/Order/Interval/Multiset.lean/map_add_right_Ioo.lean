import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]

theorem map_add_right_Ioo (a b c : α) : ((Ioo a b).map fun x => x + c) = Ioo (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact Multiset.map_add_left_Ioo _ _ _

