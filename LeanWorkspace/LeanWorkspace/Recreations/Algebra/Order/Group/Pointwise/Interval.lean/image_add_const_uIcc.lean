import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem image_add_const_uIcc : (fun x => x + a) '' [[b, c]] = [[b + a, c + a]] := by simp

