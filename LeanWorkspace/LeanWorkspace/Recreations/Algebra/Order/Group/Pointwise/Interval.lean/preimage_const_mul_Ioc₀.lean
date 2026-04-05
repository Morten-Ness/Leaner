import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem preimage_const_mul_Ioc₀ (a b : G₀) (h : 0 < c) :
    (c * ·) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]

