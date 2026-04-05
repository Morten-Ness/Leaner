import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem image_mul_left_Iic (h : 0 < a) (b : G₀) : (a * ·) '' Iic b = Iic (a * b) := (OrderIso.mulLeft₀ a h).image_Iic b

