import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}

theorem image_mul_right_Ico (a b : G₀) (h : 0 < c) :
    (fun x => x * c) '' Ico a b = Ico (a * c) (b * c) := (OrderIso.mulRight₀ c h).image_Ico a b

