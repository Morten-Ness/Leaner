import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]

theorem map_add_left_Ioc (a b c : α) : (Ioc a b).map (c + ·) = Ioc (c + a) (c + b) := by
  classical rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

