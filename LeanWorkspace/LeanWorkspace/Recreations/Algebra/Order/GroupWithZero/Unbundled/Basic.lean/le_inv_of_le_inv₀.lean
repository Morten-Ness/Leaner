import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem le_inv_of_le_inv₀ (ha : 0 < a) (h : a ≤ b⁻¹) : b ≤ a⁻¹ := (le_inv_comm₀ ha <| Right.inv_pos.1 <| ha.trans_le h).1 h

