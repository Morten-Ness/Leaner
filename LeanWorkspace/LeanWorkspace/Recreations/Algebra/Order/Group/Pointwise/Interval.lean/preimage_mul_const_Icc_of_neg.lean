import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_mul_const_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Icc a b = Icc (b / c) (a / c) := by simp [← Ici_inter_Iic, h, inter_comm]

