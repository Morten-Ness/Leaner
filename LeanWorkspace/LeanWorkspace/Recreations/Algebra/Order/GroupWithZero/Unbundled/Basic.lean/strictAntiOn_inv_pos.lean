import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem strictAntiOn_inv_pos : StrictAntiOn (fun x : G₀ ↦ x⁻¹) {r | 0 < r} := fun ⦃_⦄ ha ⦃_⦄ _ h ↦ inv_strictAnti₀ (Set.mem_setOf.mp ha) h

