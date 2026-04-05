import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}

theorem preimage_mul_const_Iic₀ (a : G₀) (h : 0 < c) : (· * c) ⁻¹' Iic a = Iic (a / c) := by
  simpa only [division_def] using (OrderIso.mulRight₀ c h).preimage_Iic a

