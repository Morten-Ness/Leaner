import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀]
  [MulPosReflectLT G₀] {a : G₀}

theorem inv_Ioo_0_left (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹ := by
  ext x
  exact ⟨fun h ↦ inv_lt_of_inv_lt₀ (inv_pos.1 h.1) h.2,
         fun h ↦ ⟨inv_pos.2 <| (inv_pos.2 ha).trans h, inv_lt_of_inv_lt₀ ha h⟩⟩

