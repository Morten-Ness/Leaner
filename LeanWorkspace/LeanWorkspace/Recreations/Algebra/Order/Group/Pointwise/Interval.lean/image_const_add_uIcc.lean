import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem image_const_add_uIcc : (fun x => a + x) '' [[b, c]] = [[a + b, a + c]] := by simp [add_comm]

