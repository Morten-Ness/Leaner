import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem lt_inv_of_lt_inv₀ (ha : 0 < a) (h : a < b⁻¹) : b < a⁻¹ := (lt_inv_comm₀ ha <| Right.inv_pos.1 <| ha.trans h).1 h

