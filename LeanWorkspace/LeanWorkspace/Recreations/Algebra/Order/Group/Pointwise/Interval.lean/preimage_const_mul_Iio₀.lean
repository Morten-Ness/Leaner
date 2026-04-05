import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem preimage_const_mul_Iio₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Iio a = Iio (a / c) := ext fun _x => (lt_div_iff₀' h).symm

