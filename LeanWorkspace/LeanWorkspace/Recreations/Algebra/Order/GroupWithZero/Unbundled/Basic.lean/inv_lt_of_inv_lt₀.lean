import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem inv_lt_of_inv_lt₀ (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a := (inv_lt_comm₀ ha <| (Right.inv_pos.2 ha).trans h).1 h

