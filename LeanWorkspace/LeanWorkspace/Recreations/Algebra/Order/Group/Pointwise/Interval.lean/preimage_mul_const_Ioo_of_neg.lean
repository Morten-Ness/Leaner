import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_mul_const_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by simp [← Ioi_inter_Iio, h, inter_comm]

