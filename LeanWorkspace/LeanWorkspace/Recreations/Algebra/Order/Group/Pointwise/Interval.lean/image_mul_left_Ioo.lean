import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem image_mul_left_Ioo (h : 0 < a) (b c : G₀) : (a * ·) '' Ioo b c = Ioo (a * b) (a * c) := (OrderIso.mulLeft₀ a h).image_Ioo b c

