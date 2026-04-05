import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_mul_const_Ici_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ici a = Iic (a / c) := ext fun _x => (le_div_iff_of_neg h).symm

