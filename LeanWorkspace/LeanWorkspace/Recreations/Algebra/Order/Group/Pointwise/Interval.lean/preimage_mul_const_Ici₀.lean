import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}

theorem preimage_mul_const_Ici₀ (a : G₀) (h : 0 < c) : (· * c) ⁻¹' Ici a = Ici (a / c) := by
  simpa only [division_def] using (OrderIso.mulRight₀ c h).preimage_Ici a

