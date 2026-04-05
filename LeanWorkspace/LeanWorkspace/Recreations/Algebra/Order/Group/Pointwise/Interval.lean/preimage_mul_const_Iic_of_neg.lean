import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_mul_const_Iic_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iic a = Ici (a / c) := ext fun _x => (div_le_iff_of_neg h).symm

