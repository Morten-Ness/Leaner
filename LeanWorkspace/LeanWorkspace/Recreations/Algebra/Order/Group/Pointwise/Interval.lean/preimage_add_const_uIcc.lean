import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem preimage_add_const_uIcc : (fun x => x + a) ⁻¹' [[b, c]] = [[b - a, c - a]] := by
  simpa only [add_comm] using Set.preimage_const_add_uIcc a b c

