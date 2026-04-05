import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_mul_const_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]

