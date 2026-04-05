import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem preimage_const_mul_Iic₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Iic a = Iic (a / c) := ext fun _x => (le_div_iff₀' h).symm

