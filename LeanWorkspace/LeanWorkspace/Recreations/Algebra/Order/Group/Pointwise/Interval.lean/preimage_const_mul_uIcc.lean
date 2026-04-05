import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_const_mul_uIcc (ha : a ≠ 0) (b c : α) :
    (a * ·) ⁻¹' [[b, c]] = [[b / a, c / a]] := by
  simp only [← Set.preimage_mul_const_uIcc ha, mul_comm]

