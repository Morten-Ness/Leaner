import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem image_sub_const_uIcc : (fun x => x - a) '' [[b, c]] = [[b - a, c - a]] := by
  simp [sub_eq_add_neg, add_comm]

