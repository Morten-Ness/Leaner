import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}

theorem image_mul_right_Icc' (a b : G₀) (h : 0 < c) :
    (· * c) '' Icc a b = Icc (a * c) (b * c) := (OrderIso.mulRight₀ c h).image_Icc a b

