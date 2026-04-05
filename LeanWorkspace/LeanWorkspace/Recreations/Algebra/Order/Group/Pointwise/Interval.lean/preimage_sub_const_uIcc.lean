import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem preimage_sub_const_uIcc : (fun x => x - a) ⁻¹' [[b, c]] = [[b + a, c + a]] := by
  simp [sub_eq_add_neg]

