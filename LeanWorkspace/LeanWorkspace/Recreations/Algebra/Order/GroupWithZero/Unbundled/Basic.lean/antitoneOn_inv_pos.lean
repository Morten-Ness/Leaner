import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem antitoneOn_inv_pos : AntitoneOn (fun x : G₀ ↦ x⁻¹) {r | 0 < r} := strictAntiOn_inv_pos.antitoneOn

