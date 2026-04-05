import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}

theorem image_mul_right_Ioc (a b : G₀) (h : 0 < c) :
    (fun x => x * c) '' Ioc a b = Ioc (a * c) (b * c) := (OrderIso.mulRight₀ c h).image_Ioc a b

