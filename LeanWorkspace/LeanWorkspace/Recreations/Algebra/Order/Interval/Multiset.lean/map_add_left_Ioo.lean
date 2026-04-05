import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]

theorem map_add_left_Ioo (a b c : α) : (Ioo a b).map (c + ·) = Ioo (c + a) (c + b) := by
  classical rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

