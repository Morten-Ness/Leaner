import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

theorem preimage_const_sub_uIcc : (fun x => a - x) ⁻¹' [[b, c]] = [[a - b, a - c]] := by
  simp_rw [← Icc_min_max, preimage_const_sub_Icc]
  simp only [sub_eq_add_neg, min_add_add_left, max_add_add_left, min_neg_neg, max_neg_neg]

-- simp can prove this modulo `add_comm`

