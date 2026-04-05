import Mathlib

variable {α β : Type*}

theorem map_tsub_of_le {F : Type*} [PartialOrder α] [AddCommSemigroup α] [ExistsAddOfLE α]
    [AddLeftMono α] [Sub α] [OrderedSub α] [PartialOrder β] [AddCommSemigroup β] [Sub β]
    [OrderedSub β] [AddLeftReflectLE β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : α) (h : b ≤ a) : f a - f b = f (a - b) := by
  conv => lhs; rw [← tsub_add_cancel_of_le h]
  rw [map_add, add_tsub_cancel_right]

