import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem preimage_const_add_uIcc : (fun x => a + x) ⁻¹' [[b, c]] = [[b - a, c - a]] := by
  simp only [← Icc_min_max, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]

