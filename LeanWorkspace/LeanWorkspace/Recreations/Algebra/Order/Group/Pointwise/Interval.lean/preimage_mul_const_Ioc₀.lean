import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}

theorem preimage_mul_const_Ioc₀ (a b : G₀) (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]

