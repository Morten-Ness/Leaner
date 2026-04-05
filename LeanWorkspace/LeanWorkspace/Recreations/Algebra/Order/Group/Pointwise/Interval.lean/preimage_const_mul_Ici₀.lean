import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem preimage_const_mul_Ici₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Ici a = Ici (a / c) := ext fun _x => (div_le_iff₀' h).symm

