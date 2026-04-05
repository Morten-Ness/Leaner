import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_mul_const_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]

