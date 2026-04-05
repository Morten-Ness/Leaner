import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀]
  [MulPosReflectLT G₀] {a : G₀}

theorem inv_Ioi₀ (ha : 0 < a) : (Ioi a)⁻¹ = Ioo 0 a⁻¹ := by
  rw [inv_eq_iff_eq_inv, Set.inv_Ioo_0_left (inv_pos.2 ha), inv_inv]

