import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]

theorem map_add_right_Ioc (a b c : α) : ((Ioc a b).map fun x => x + c) = Ioc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact Multiset.map_add_left_Ioc _ _ _

