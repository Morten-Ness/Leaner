import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem image_const_sub_uIcc : (fun x => a - x) '' [[b, c]] = [[a - b, a - c]] := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

