import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}

theorem preimage_mul_const_Icc₀ (a b : G₀) (h : 0 < c) :
    (· * c) ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]

