import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem image_mul_left_Ico (h : 0 < a) (b c : G₀) :
    (a * ·) '' Ico b c = Ico (a * b) (a * c) := (OrderIso.mulLeft₀ a h).image_Ico b c

