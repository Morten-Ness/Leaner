import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem preimage_const_mul_Ico₀ (a b : G₀) (h : 0 < c) :
    (c * ·) ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]

