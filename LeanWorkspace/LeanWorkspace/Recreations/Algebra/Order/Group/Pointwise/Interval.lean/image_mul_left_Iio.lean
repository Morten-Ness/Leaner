import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem image_mul_left_Iio (h : 0 < a) (b : G₀) : (a * ·) '' Iio b = Iio (a * b) := (OrderIso.mulLeft₀ a h).image_Iio b

