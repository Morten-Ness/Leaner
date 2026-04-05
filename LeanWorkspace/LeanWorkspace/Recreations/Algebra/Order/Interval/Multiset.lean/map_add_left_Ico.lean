import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]

theorem map_add_left_Ico (a b c : α) : (Ico a b).map (c + ·) = Ico (c + a) (c + b) := by
  classical rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

