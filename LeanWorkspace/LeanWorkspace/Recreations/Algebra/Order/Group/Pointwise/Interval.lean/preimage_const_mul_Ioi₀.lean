import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem preimage_const_mul_Ioi₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Ioi a = Ioi (a / c) := ext fun _x => (div_lt_iff₀' h).symm

