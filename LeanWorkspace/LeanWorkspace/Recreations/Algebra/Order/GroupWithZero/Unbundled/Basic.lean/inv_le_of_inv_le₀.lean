import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem inv_le_of_inv_le₀ (ha : 0 < a) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a := (inv_le_comm₀ ha <| (Right.inv_pos.2 ha).trans_le h).1 h

