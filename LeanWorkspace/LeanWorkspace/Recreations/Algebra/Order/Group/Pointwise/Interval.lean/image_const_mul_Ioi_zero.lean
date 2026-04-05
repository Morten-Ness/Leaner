import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem image_const_mul_Ioi_zero (ha : 0 < a) :
    (a * ·) '' Ioi 0 = Ioi 0 := by
  rw [Set.image_mul_left_Ioi ha, mul_zero]

