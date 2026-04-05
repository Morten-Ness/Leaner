import Mathlib

variable {F α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_two_inv : round (2⁻¹ : α) = 1 := by norm_num [round_eq_iff]

